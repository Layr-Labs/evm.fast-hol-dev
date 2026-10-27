(* Retain all translator preconditions while computing an untrusted hint.
   This derives a local variant of the pinned HOL cv translator. It changes
   dependency translation from requiring totality to returning a conditional
   representation theorem. No theorem assumptions are discharged here.
   Callers must validate the resulting candidate independently. *)
structure decoderHintLib :> decoderHintLib = struct
open HolKernel;
fun read path =
  let val stream = TextIO.openIn path
      val source = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
  in source end;
fun replace_once old replacement source =
  let val n = size old
      fun find i =
        if i+n > size source then raise Fail "pinned cv translator has changed"
        else if String.substring(source,i,n) = old then i else find (i+1)
      val i = find 0
      val rest = String.extract(source,i+n,NONE)
      val _ = if String.isSubstring old rest then
                raise Fail "ambiguous cv translator patch" else ()
  in String.substring(source,0,i) ^ replacement ^ rest end;
fun quote s = "\"" ^ String.toString s ^ "\"";
fun translate thy definition =
  let val path = OS.Path.concat (Globals.HOLDIR,
        "src/num/theories/cv_compute/automation/cv_transLib.sml")
      val source = read path
        |> replace_once "structure cv_transLib :> cv_transLib ="
             "structure decoderHintTranslator :> cv_transLib ="
        |> replace_once "NONE => cv_trans_any NONE NONE def"
             "NONE => cv_trans_any (SOME \"\") NONE def"
      val source = replace_once "val new_def = find_inst_def_for needs_c"
        "val new_def = find_inst_def_for needs_c |> PURE_REWRITE_RULE [FUN_EQ_THM]" source
      val source = source ^ "\nval _ = decoderHintTranslator.cv_auto_trans_pre \"\" (DB.fetch " ^
        quote thy ^ " " ^ quote definition ^ ");\n"
      val offset = ref 0
      fun next () = if !offset = size source then NONE
        else let val c = String.sub(source,!offset)
             in offset := !offset+1; SOME c end
      fun compile () = if !offset = size source then ()
        else (PolyML.compiler(next,[PolyML.Compiler.CPFileName path])(); compile ())
  in compile () end;
end
