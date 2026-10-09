#!/usr/bin/env python3
"""Author-only parallel diagnostics: imports built predecessors, NOT acceptance.

Imported predecessor names and TypeBase state differ from a production replay.
The diagnostic copy extends fixed_eval's candidate guard to mapped predecessor
theories, preventing native EVAL from bypassing that production restriction.
Other differences remain. Passing diagnostics are useful for
finding local gaps; only the full verifier establishes certificate acceptance.
"""
import argparse
import concurrent.futures
import fcntl
import hashlib
import json
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def parents(build, name):
    path = build / ".hol/objs" / (name + "Theory.sml")
    text = path.read_text()
    match = re.search(r"local\s+open\s+(.*?)\s+in\s+end\s*;", text, re.S)
    if match is None:
        raise ValueError(f"Cannot identify compiled theory parents: {path}")
    modules = match[1].split()
    if any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", m) for m in modules):
        raise ValueError(f"Unexpected parent metadata: {path}")
    result = [m[:-6] for m in modules if m.endswith("Theory")]
    if name in result:
        raise ValueError(f"Self dependency: {name}")
    return result


def quote(value):
    value = str(value)
    if any(ord(c) < 32 or ord(c) > 126 for c in value):
        raise ValueError("SML paths must contain printable ASCII characters")
    return json.dumps(value)


def driver(name, deps, build, article, prior, verifier, diagnose_eval=False):
    loads = "\n".join("load " + quote(d + "Theory") + ";" for d in deps)
    roots = ",".join(map(quote, ["OpenTheoryReaderContext", "initProofLibrary"] + deps))
    allowed = ",".join(map(quote, prior))
    diagnostic = r"""
fun bounded_pretty tm =
 if strictReplayLib.bounded_term 8192 tm then
   let val text = term_to_string tm
   in if size text <= 40000 then text
      else String.substring(text,0,40000) ^ "...[truncated]" end
 else (sketch_budget := 2000; sketch 40 tm);
fun diagnose c =
 if not (strictReplayLib.bounded_term 8192 c) then
   print "EVAL_DIAGNOSTIC_SKIPPED request exceeds8192nodes\n"
 else
   (print("REQUEST_PRETTY " ^ bounded_pretty c ^ "\n");
    print("REQUEST_TYPE " ^ type_to_string(type_of c) ^ "\n");
    print("REQUEST_TYPE_VARIABLES " ^
      String.concatWith "," (map type_to_string (type_vars_in_term c)) ^ "\n");
    print("REQUEST_FREE_VARIABLES " ^
      String.concatWith "," (map (fn v => #1(dest_var v) ^ ":" ^
        type_to_string(type_of v)) (free_vars c)) ^ "\n");
    ((ignore(strictReplayLib.fixed_eval c); print "FIXED_EVAL_RETURNED\n")
      handle ex => print("FIXED_EVAL_ERROR " ^ exception_text ex ^ "\n"));
    ((let val evaluated = bossLib.EVAL c
          val residual = rhs(concl evaluated)
      in print("EVAL_RESIDUAL " ^ bounded_pretty residual ^ "\n") end)
      handle ex => print("EVAL_ERROR " ^ exception_text ex ^ "\n")))
 handle ex => print("EVAL_DIAGNOSTIC_ERROR " ^ exception_text ex ^ "\n");
""" if diagnose_eval else 'fun diagnose _ = ();\n'
    return f'''val _ = PolyML.print_depth 0;
open HolKernel boolLib bossLib;
val _ = loadPath := [{quote(build)}, {quote(build / '.hol/objs')}] @ !loadPath;
{loads}
(* Match operator heap setup even when diagnosing from an older saved heap. *)
val _ = load "wordsLib";
val _ = print "DIAGNOSTIC_PREDECESSORS_LOADED\\n";
val _ = QUse.use {quote(verifier / 'articleReaderLib.sml')};
val _ = QUse.use {quote(verifier / 'strictReplayLib.sml')};
val roots = [{roots}];
val fixed = Lib.mk_set (List.concat (map (fn thy => thy :: ancestry thy) roots));
val _ = if List.exists (fn thy => thy = {quote(name)}) fixed
        then raise Fail "Diagnostic imported its target theory" else ();
val trusted = strictReplayLib.kernel_axioms @ List.concat
 (map (fn thy => map snd (DB.definitions thy @ DB.theorems thy)) fixed);
val prior = [{allowed}];
val _ = new_theory "candidateCertificate";
fun prior_name (n as (["HOL4","candidateCertificate"],name)) =
 (case String.fields (fn c => c = #"_") name of
    thy::""::rest => if List.exists (fn x => x=thy) prior andalso
                       List.exists (fn x => x=thy) fixed
      then (["HOL4",thy],String.concatWith "_" rest) else n
  | _ => n)
 | prior_name n = n;
fun exception_text (HOL_ERR error) = Feedback.top_structure_of error ^ "." ^
 Feedback.top_function_of error ^ ": " ^ Feedback.message_of error
 | exception_text e = General.exnName e;
val sketch_budget = ref 2000;
fun sketch depth tm = if !sketch_budget = 0 then "..."
 else (sketch_budget := !sketch_budget - 1; sketch_body depth tm)
and sketch_body depth tm = if depth=0 then "..." else
 if is_var tm then #1(dest_var tm) else if is_const tm then
 let val {{Thy,Name,...}}=dest_thy_const tm in Thy ^ "$" ^ Name end
 else if is_comb tm then let val (f,x)=dest_comb tm in
 "(" ^ sketch(depth-1) f ^ " " ^ sketch(depth-1) x ^ ")" end
 else let val(v,b)=dest_abs tm in "(lambda " ^ #1(dest_var v) ^ ". " ^ sketch(depth-1) b ^ ")" end;
{diagnostic}
val _ = print("DIAGNOSTIC_INDEXING " ^ Int.toString(length trusted) ^ " facts\\n");
val base = strictReplayLib.reader trusted;
val _ = print "DIAGNOSTIC_READER_READY\\n";
val requests = ref 0;
val reader = {{const_name= #const_name base o prior_name,
 tyop_name= #tyop_name base o prior_name,
 define_const= #define_const base, define_tyop= #define_tyop base,
 axiom=fn proved => fn seq as (hs,c) =>
  (requests := !requests+1;
   #axiom base proved seq handle e =>
    (sketch_budget := 2000; print("FAILED_REQUEST " ^ Int.toString(!requests) ^ " " ^ sketch 40 c ^ "\\n");
     diagnose c;
     raise e))}};
val _ = ((let
 val input = TextIO.openIn {quote(article)};
 val result = articleReaderLib.raw_read_article input reader;
 val _ = TextIO.closeIn input;
 in print("ARTICLE_DIAGNOSTIC_OK " ^ Int.toString(length(Net.listItems result)) ^ "\\n");
    OS.Process.exit OS.Process.success end)
 handle e => (print("DIAGNOSTIC_ERROR " ^ exception_text e ^ "\\n");
              OS.Process.exit OS.Process.failure));
'''


def atomic_json(path, data):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    temporary.replace(path)


def run_one(name, args, common, plan):
    article = args.exports / name / "proof.art"
    deps = parents(args.build, name)
    output = args.output / name
    output.mkdir(parents=True, exist_ok=True)
    prior = plan[:plan.index(name)]
    runtime = output / "runtime"
    runtime.mkdir(exist_ok=True)
    guard = "#Thy (dest_thy_const tm) = current_theory ()"
    strict = (args.snapshot / "strictReplayLib.sml").read_text()
    if strict.count(guard) != 1:
        raise ValueError("Expected exactly one fixed_eval candidate guard")
    expanded_guard = "(" + guard + " orelse List.exists (fn thy => thy = #Thy (dest_thy_const tm)) [" + ",".join(map(quote, prior)) + "])"
    strict = strict.replace(guard, expanded_guard)
    (runtime / "strictReplayLib.sml").write_text(strict)
    (runtime / "articleReaderLib.sml").write_bytes((args.snapshot / "articleReaderLib.sml").read_bytes())
    script = driver(name, deps, args.build, article, prior, runtime, args.diagnose_eval)
    seen = set()

    def visit(theory):
        if theory in seen:
            return
        seen.add(theory)
        data = args.build / ".hol/objs" / (theory + "Theory.dat")
        if data.exists():
            for parent in parents(args.build, theory):
                visit(parent)

    for dep in deps:
        visit(dep)
    predecessor_hashes = {
        dep: digest(args.build / ".hol/objs" / (dep + "Theory.dat"))
        for dep in sorted(seen)
        if (args.build / ".hol/objs" / (dep + "Theory.dat")).exists()}
    fingerprint = dict(common, article=digest(article),
                       diagnostic_strict_replay=hashlib.sha256(strict.encode()).hexdigest(),
                       script=hashlib.sha256(script.encode()).hexdigest(),
                       predecessor_hashes=predecessor_hashes)
    result_path = output / "result.json"
    if args.resume and result_path.exists():
        previous = json.loads(result_path.read_text())
        if previous.get("fingerprint") == fingerprint and previous.get("status") == "passed":
            print(f"CACHED {name}", flush=True)
            return previous
    script_path = output / "replay.sml"
    script_path.write_text(script)
    # Workers use immutable batch snapshots; production edits may continue.
    for source, key in (("articleReaderLib.sml", "reader"), ("strictReplayLib.sml", "strict_replay")):
        if digest(args.snapshot / source) != common[key]:
            raise ValueError("Diagnostic source snapshot changed during batch")
    command = [str(args.hol / "bin/hol"), "--maxheap", str(args.heap_gib * 1024),
               "--gcthreads=1", "--holstate=" + str(args.heap), str(script_path)]
    start = time.monotonic()
    print(f"START {name} (imports {', '.join(deps)})", flush=True)
    status, returncode = "failed", None
    with (output / "replay.log").open("w") as log:
        process = subprocess.Popen(command, cwd=output, stdout=log, stderr=subprocess.STDOUT)
        atomic_json(output / "running.json", {"pid": process.pid, "command": command})
        try:
            returncode = process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            status = "timeout"
    text = (output / "replay.log").read_text(errors="replace")
    if returncode == 0 and "ARTICLE_DIAGNOSTIC_OK " in text:
        status = "passed"
    if returncode is not None and returncode < 0:
        status = "terminated"
    elif status != "passed" and "Run out of store - interrupting threads" in text:
        status = "resource_exhausted"
    result = {"module": name, "status": status, "exit": returncode,
              "wall_seconds": time.monotonic() - start, "fingerprint": fingerprint,
              "independent_acceptance": False,
              "diagnostic_trust": "imports already-built predecessor theories"}
    if returncode is not None and returncode < 0:
        result["signal"] = signal.Signals(-returncode).name
        result["infrastructure_failure"] = True
    elif status == "resource_exhausted":
        result["resource"] = "HOL heap"
        result["infrastructure_failure"] = True
    atomic_json(result_path, result)
    (output / "running.json").unlink(missing_ok=True)
    print(f"{status.upper()} {name} ({result['wall_seconds']:.1f}s)", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*", help="Selected modules, in scheduling order; default plan order")
    parser.add_argument("--exports", type=Path, default=ROOT / ".export-baseline-checkpoint")
    parser.add_argument("--build", type=Path, default=ROOT / ".build-hol-compatible")
    parser.add_argument("--heap", type=Path, default=ROOT / ".build/verifier.heap")
    parser.add_argument("--hol", type=Path, default=ROOT.parent / "HOL-init-e")
    parser.add_argument("--output", type=Path, default=ROOT / ".export-baseline-checkpoint/audit")
    parser.add_argument("--workers", type=int, default=3, help="Concurrent HOL workers (default: 3)")
    parser.add_argument("--heap-gib", type=int, default=24)
    parser.add_argument("--timeout", type=int, default=7200)
    parser.add_argument("--diagnose-eval", action="store_true", help="On failure, inspect fixed EVAL and its residual (opt-in;8192-node limit, worker timeout applies)")
    parser.add_argument("--resume", action="store_true", help="Reuse successful results with matching content hashes")
    parser.add_argument("--list", action="store_true", help="Print modules and compiled direct parents without launching HOL")
    args = parser.parse_args()
    if min(args.workers, args.heap_gib, args.timeout) < 1:
        parser.error("workers, heap-gib, timeout must be positive")
    for key in ("exports", "build", "heap", "hol", "output"):
        setattr(args, key, getattr(args, key).resolve())
    plan = json.loads((args.exports / "plan.json").read_text())
    if not isinstance(plan, list) or any(not isinstance(n, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", n) for n in plan):
        parser.error("invalid export plan")
    unknown = set(args.modules) - set(plan)
    if unknown:
        parser.error("unknown modules: " + ", ".join(sorted(unknown)))
    selected = list(dict.fromkeys(args.modules)) if args.modules else plan
    if args.list:
        for name in selected:
            print(name + ": " + " ".join(parents(args.build, name)))
        return 0
    args.output.mkdir(parents=True, exist_ok=True)
    # Prevent accidentally running overlapping orchestrators in this output.
    with (args.output / "runner.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        common = {"heap": digest(args.heap), "runner": digest(Path(__file__)),
                  "reader": digest(ROOT / "verifier/articleReaderLib.sml"),
                  "strict_replay": digest(ROOT / "verifier/strictReplayLib.sml"),
                  "heap_gib": args.heap_gib, "timeout": args.timeout}
        args.snapshot = args.output / ("sources-" + common["reader"][:12] + "-" + common["strict_replay"][:12])
        args.snapshot.mkdir(exist_ok=True)
        for source, key in (("articleReaderLib.sml", "reader"), ("strictReplayLib.sml", "strict_replay")):
            data = (ROOT / "verifier" / source).read_bytes()
            if hashlib.sha256(data).hexdigest() != common[key]:
                raise ValueError("Verifier changed during snapshot")
            (args.snapshot / source).write_bytes(data)
        print("AUTHOR DIAGNOSTICS ONLY; these results do not establish certificate acceptance", flush=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(run_one, name, args, common, plan): name for name in selected}
            results = []
            for future in concurrent.futures.as_completed(futures):
                name = futures[future]
                try:
                    result = future.result()
                except Exception as error:
                    result = {"module": name, "status": "error", "error": str(error),
                              "independent_acceptance": False}
                    print(f"ERROR {name}: {error}", flush=True)
                results.append(result)
                atomic_json(args.output / "summary.json", results)
        return 0 if all(r["status"] == "passed" for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
