#!/usr/bin/env python3
"""Export baseline-specific HOL proofs for independent strict article replay.

Build initBaselineCertificateTheory and initProofLibraryTheory with standard
HOL first, and prepare a separate tracing HOL with prepare_exporter.py.
Standard theory files supply author-side premises; the article verifier must
resolve every such premise from its fixed library or earlier article proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from compact_article import compact

ROOT = Path(__file__).resolve().parents[1]


def theory_sources():
    return {p.stem[:-6]: p for directory in ('challenge', 'experiments')
            for p in (ROOT/directory).glob('*Script.sml')}


def source_modules(source):
    text = re.sub(r'\(\*.*?\*\)', '', source.read_text(), flags=re.S)
    ancestors = re.search(r'^Ancestors\s+(.*?)^Libs\b', text, re.M | re.S)
    modules = [] if ancestors is None else [name+'Theory' for name in ancestors[1].split()]
    start = re.search(r'^Libs\b', text, re.M)
    if start:
        for line in text[start.end():].splitlines():
            line = line.strip()
            if not line:
                continue
            if not re.fullmatch(r'[A-Za-z0-9_ \t\[\]]+', line) or line.split()[0] in {
                    'open', 'val', 'fun', 'local', 'in', 'end', 'Definition', 'Theorem'}:
                break
            modules.extend(re.sub(r'\[[^]]*\]', '', line).split())
    modules.extend(re.findall(r'\b([A-Za-z][A-Za-z0-9_]*)\.', text))
    return list(dict.fromkeys(modules))


def dependencies(build, name):
    source = theory_sources()[name]
    standard = Path((build/'hol-path.txt').read_text())
    paths = {}
    for directory in [standard, build]:
        for path in directory.rglob('*.uo'):
            logical = path.parent.parent.parent/path.name if path.parent.name == "objs" and path.parent.parent.name == ".hol" else path
            paths[path.stem] = logical
    return [str(paths[module]) for module in source_modules(source) if module in paths]


def local_closure(build, sources, root):
    ordered, seen = [], set()
    def visit(name):
        if name in seen or name not in sources:
            return
        seen.add(name)
        for dependency in source_modules(sources[name]):
            match = re.fullmatch(r'(\w+)Theory', dependency)
            if match:
                visit(match[1])
        ordered.append(name)
    visit(root)
    return ordered


def author_setup(build, standard, deps, candidates):
    q = json.dumps
    return f'''val _ = PolyML.print_depth 0;
val _ = TraceMode.mode := TraceMode.TraceOnly;
load "Logging";
val _ = holpathdb.extend_db {{vname="HOLDIR",path={q(str(standard))}}};
val _ = holpathdb.extend_db {{vname="init-e-hol4",path={q(str(ROOT))}}};
val _ = loadPath := {q([str(build/'.hol/objs'),str(build),str(standard/'sigobj')])} @ !loadPath;
val _ = List.app load {q(deps)};
val candidate_theories = {q(candidates)};
fun article_name thy name =
 if List.exists (fn t => t=thy) candidate_theories
 then (["HOL4","candidateCertificate"],thy ^ "__" ^ name)
 else (["HOL4",thy],name);
val _ = Logging.set_const_name_handler
 (fn {{Thy,Name}} => article_name Thy Name);
val _ = Logging.set_tyop_name_handler
 (fn {{Thy,Tyop}} => article_name Thy Tyop);
'''


def driver(build, standard, source, target, candidates, article):
    q = json.dumps
    deps = [str(Path(dep).with_suffix('')) for dep in dependencies(build, target)]
    return author_setup(build, standard, deps, candidates) + f'''val _ = Theory.register_hook ("article-export",fn delta => case delta of
 TheoryDelta.NewTheory {{newseg,...}} =>
  if newseg={q(target)} then Logging.raw_start_logging [] (TextIO.openOut {q(str(article))}) else ()
| TheoryDelta.NewBinding (_,(th,_)) =>
  if Theory.current_theory ()={q(target)} then ignore (Logging.export_thm th) else ()
| _ => ());
val _ = QUse.use {q(str(source))};
val _ = List.app (fn (_,th) => ignore (Logging.export_thm th))
 (DB.definitions {q(target)} @ DB.theorems {q(target)});
val _ = Logging.stop_logging ();
val _ = print "BASELINE_MODULE_EXPORT_OK\\n";
'''


def allocation_hint(build, standard, work, runtime):
    """Reuse data from the prior build; the recorded compiler checks this hint."""
    q = json.dumps
    output = work/'allocation.term'
    script = work/'extract_hint.sml'
    script.write_text(f'''val _ = PolyML.print_depth 0;
val _ = holpathdb.extend_db {{vname="init-e-hol4",path={q(str(ROOT))}}};
val _ = loadPath := {q([str(build),str(build/'.hol/objs')])} @ !loadPath;
load "initBytecodeTheory";
load "sptreeSyntax";
load "optionSyntax";
open HolKernel;
val _ = QUse.use {q(str(ROOT/'tools/allocationHintLib.sml'))};
val hint = boolSyntax.rhs (concl initBytecodeTheory.allocation_def);
val _ = allocationHintLib.write {q(str(output))} hint;
val _ = if aconv (allocationHintLib.read {q(str(output))}) hint then ()
        else raise Fail "allocation hint round trip failed";
val _ = print "ALLOCATION_HINT_EXTRACTED\\n";
''')
    with (work/'hint.log').open('w') as log:
        result = subprocess.run([str(standard/'bin/hol'), *runtime, 'run',
            str(standard/'sigobj/holmake_not_interactive.uo'), str(script)],
            cwd=work, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode or 'ALLOCATION_HINT_EXTRACTED' not in (work/'hint.log').read_text():
        raise RuntimeError(f'Hint extraction failed (exit {result.returncode}): {work/"hint.log"}')
    return output


def author_source(source, target, work, hint=None):
    if target == 'initDecodedConfig':
        text = source.read_text()
        # The decoder result supplies data only; the unconditional re-encoding
        # theorem below is still recorded and independently checked.
        text = text.replace('val hint_result = cv_eval',
            'val hint_result = Lib.with_flag (TraceMode.mode,TraceMode.NoTrace) cv_eval')
        compact = """fun compact_eval tm =
  Lib.with_flag (TraceMode.mode,TraceMode.NoTrace) EVAL tm;
fun compact_record_literal tm =
  if TypeBase.is_record tm andalso not (null (#2 (TypeBase.dest_record tm)))
     andalso not (TypeBase.is_constructor (fst (strip_comb tm))) then
    (REWR_CONV (recordLiteralLib.reconstruction (type_of tm)) THENC compact_eval) tm
  else NO_CONV tm;
val compact_record_normalize = compact_eval THENC
  TOP_DEPTH_CONV compact_record_literal THENC compact_eval THENC
  REWRITE_CONV [cvTheory.b2c_def] THENC compact_eval;
"""
        text = text.replace('val candidateConfig_def =', compact + 'val candidateConfig_def =')
        text = text.replace('cv_trans_deep_embedding recordLiteralLib.normalize',
                            'cv_trans_deep_embedding compact_record_normalize')
        result = work/'initDecodedConfigScript.sml'
        result.write_text(text)
        return result
    if target == 'initConfigNumbers':
        text = source.read_text().replace('cv_trans_deep_embedding EVAL config_numbers_def',
            'cv_trans_deep_embedding (Lib.with_flag (TraceMode.mode,TraceMode.NoTrace) EVAL) config_numbers_def')
        result = work/'initConfigNumbersScript.sml'
        result.write_text(text)
        return result
    if target in ('initBootstrapSuffixSteps', 'initBootstrapChallengeSuffixSteps'):
        text = source.read_text()
        marker = ('Theorem bootstrap_challenge_suffix_steps:' if 'Challenge' in target
                  else 'Theorem bootstrap_suffix_steps:')
        compact = """(* Export each solved instruction goal before constructing the final
   conjunction, retaining checked sequents instead of all primitive traces. *)
fun compact_suffix_step pc goal context =
  let val (goals,validate) = suffix_step_tac pc goal context
  in if null goals then
       let val th = validate []
           val _ = Logging.export_thm th
           val _ = Logging.flush_dictionary ()
           val _ = PolyML.fullGC ()
       in ([],fn _ => th) end
     else (goals,validate)
  end;
"""
        helpers = """val _ = List.app (ignore o Logging.export_thm)
  (enc_lengths @ membership @ state_rules @ memory_rules @ failure_rules);
val _ = Logging.flush_dictionary ();
val _ = PolyML.fullGC ();
"""
        text = text.replace('Theorem suffix_store_below:', helpers + 'Theorem suffix_store_below:')
        text = text.replace(marker, compact + marker)
        text = text.replace('conj_tac >- suffix_step_tac pc', 'conj_tac >- compact_suffix_step pc')
        text = text.replace('suffix_step_tac (List.last pcs)', 'compact_suffix_step (List.last pcs)')
        result = work/(target + 'Script.sml')
        result.write_text(text)
        return result
    if target == 'initBaselineRefinement':
        text = source.read_text().replace('EVAL_TAC', 'compact_EVAL_TAC')
        marker = 'Theorem compiler_target_config:'
        conversion = """(* Computed leaves are checked again by the standard EVAL converter. *)
fun compact_EVAL tm =
  let
    val expanded = QCONV (REWRITE_CONV
      [initCompilationInputTheory.guestConfig_def,
       initCompilationInputTheory.pancakeRiscvConfig_def]) tm;
    val input = rhs (concl expanded);
    val unresolved = List.filter
      (fn c => List.exists (fn thy => thy = #Thy (dest_thy_const c)) candidate_theories)
      (find_terms is_const input);
    val _ = if null unresolved then () else
      (List.app (fn c => let val {Thy,Name,...} = dest_thy_const c
        in print ("EVAL_CANDIDATE " ^ Thy ^ "$" ^ Name ^ "\\n") end) unresolved;
       raise Fail "candidate constant in EVAL export");
    val evaluated = Lib.with_flag (TraceMode.mode,TraceMode.NoTrace) EVAL input;
  in TRANS expanded evaluated end
  handle e => (print ("EVAL_EXPORT_ERROR " ^ General.exnMessage e ^ "\\n"); raise e);
val compact_EVAL_TAC = CONV_TAC compact_EVAL;
"""
        text = text.replace(marker, conversion + marker)
        result = work/'initBaselineRefinementScript.sml'
        result.write_text(text)
        return result
    if target != 'initBytecode':
        return source
    text = source.read_text()
    first = text.index('val _ = report "computing register-allocation graphs";')
    last = text.index('val allocation_def =', first)
    # No theorem is imported here. The from_word_0_riscv computation below
    # checks the whole hint and is recorded for independent replay.
    replacement = f'''val _ = report "reading untrusted allocation hint";
val _ = QUse.use {json.dumps(str(ROOT/'tools/allocationHintLib.sml'))};
val colours = allocationHintLib.read {json.dumps(str(hint))};
'''
    result = work/'initBytecodeScript.sml'
    recorded = text[:first]+replacement+text[last:]
    recorded = recorded.replace('cv_trans_deep_embedding EVAL allocation_def',
        'cv_trans_deep_embedding (Lib.with_flag (TraceMode.mode,TraceMode.NoTrace) EVAL) allocation_def')
    result.write_text(recorded)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hol', type=Path, required=True)
    parser.add_argument('--author-hol', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, default=ROOT/'.build')
    parser.add_argument('--output', type=Path, default=ROOT/'.export-baseline')
    parser.add_argument('--stop-before', help='stop before this theory when exporting a suffix')
    parser.add_argument('--maxheap-mib', type=int, default=24576, help='Poly/ML heap limit per worker (default: 24576 MiB)')
    parser.add_argument('--gc-threads', type=int, default=1)
    parser.add_argument('--resume', action='store_true', help='reuse unchanged author articles; final independent replay is still required')
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument('--only', help='export just one module from the baseline closure')
    selection.add_argument('--start-at', help='export this module and those following it in dependency order')
    args = parser.parse_args()
    if args.maxheap_mib < 1 or args.gc_threads < 1:
        parser.error('worker heap limit and GC thread count must be positive')
    runtime = ['--maxheap', str(args.maxheap_mib), '--gcthreads='+str(args.gc_threads)]
    standard, author = args.hol.resolve(), args.author_hol.resolve()
    if standard == author:
        parser.error('author and verifier HOL builds must be separate')
    build, output = args.build_dir.resolve(), args.output.resolve()
    if not (build/'hol-path.txt').is_file() or (build/'hol-path.txt').read_text() != str(standard):
        parser.error('--build-dir must belong to the specified standard HOL checkout')
    sources = theory_sources()
    fixed = set(local_closure(build, sources, 'initProofLibrary'))
    candidates = [name for name in local_closure(build, sources, 'initBaselineCertificate')
                  if name not in fixed]
    output.mkdir(parents=True, exist_ok=True)
    (output/'plan.json').write_text(json.dumps(candidates, indent=2)+'\n')
    selected = args.only or args.start_at
    if selected and selected not in candidates:
        parser.error('selection must name a baseline-specific theory')
    todo = [args.only] if args.only else candidates[candidates.index(args.start_at):] if args.start_at else candidates
    if args.stop_before:
        if args.only or args.stop_before not in todo:
            parser.error('--stop-before must name a theory in the selected suffix')
        todo = todo[:todo.index(args.stop_before)]
    for target in todo:
        work = output/target
        work.mkdir(exist_ok=True)
        article = work/'proof.art'
        script = work/'export.sml'
        hint = allocation_hint(build, standard, work, runtime) if target == "initBytecode" else None
        recorded_source = author_source(sources[target], target, work, hint)
        contents = driver(build, standard, recorded_source, target, candidates, article)
        stamp = work/'complete.json'
        key_material = contents + recorded_source.read_text()
        if hint is not None:
            key_material += hint.read_text() + (ROOT/"tools/allocationHintLib.sml").read_text()
        key = hashlib.sha256(key_material.encode()).hexdigest()
        if args.resume and stamp.is_file() and article.is_file():
            info = json.loads(stamp.read_text())
            with article.open('rb') as stream:
                digest = hashlib.file_digest(stream, 'sha256').hexdigest()
            if info == {'driver': key, 'article': digest}:
                print(f'Reusing author article {target}; independent replay still required', flush=True)
                continue
        script.write_text(contents)
        print(f'Exporting {target}', flush=True)
        with (work/'export.log').open('w') as log:
            result = subprocess.run([str(author/'bin/hol'), *runtime, 'run',
                str(author/'sigobj/holmake_not_interactive.uo'), str(script)],
                cwd=work, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode or 'BASELINE_MODULE_EXPORT_OK' not in (work/'export.log').read_text():
            raise RuntimeError(f'Export failed (exit {result.returncode}): {work/"export.log"}')
        compacted = work/'proof.compact.art'
        compact(article, compacted)
        compacted.replace(article)
        with article.open('rb') as stream:
            digest = hashlib.file_digest(stream, 'sha256').hexdigest()
        stamp.write_text(json.dumps({'driver': key, 'article': digest})+'\n')
        print(f'Exported {target}: {article.stat().st_size} article bytes', flush=True)
    print('Module export finished; full package assembly and replay are separate checks.')


if __name__ == '__main__':
    main()
