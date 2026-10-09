(* Compact call-edge data for constructing an untrusted ranking witness. *)
Theory initStackEdges
Ancestors initStackInput
Libs preamble cv_transLib
open wordLangTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
Definition callTargets_def:
  (callTargets (wordLang$Seq p q:64 wordLang$prog) = callTargets p ++ callTargets q) /\
  (callTargets (wordLang$If _ _ _ p q) = callTargets p ++ callTargets q) /\
  (callTargets (wordLang$Call ret dest args handler) =
    (case dest of NONE => [] | SOME d => [d]) ++
    (case ret of NONE => [] | SOME (_,_,p,_,_) => callTargets p) ++
    (case handler of NONE => [] | SOME (_,p,_,_) => callTargets p)) /\
  (callTargets (wordLang$MustTerminate p) = callTargets p) /\
  (callTargets (wordLang$Loop _ p _) = callTargets p) /\
  (callTargets _ = [])
Termination
  WF_REL_TAC `measure (prog_size (K 0))` >> rw [] >>
  simp [wordLangTheory.prog_size_def]
End
val _ = cv_auto_trans callTargets_def;
Definition optimized_edges_def:
  optimized_edges = MAP (\(n,a,p). (n,callTargets p)) optimized_word
End
val _ = cv_auto_trans optimized_edges_def;
val edges = cv_eval ``optimized_edges``;
val _ = if null(hyp edges) then save_thm("optimized_edges_value",check_thm edges)
  else failwith "edge computation assumptions";
val stream = TextIO.openOut "stack-edges.txt";
val _ = List.app (fn t =>
  let val (n,ds) = pairSyntax.dest_pair t
      val ns = n :: fst(listSyntax.dest_list ds)
  in TextIO.output(stream,
       String.concatWith " " (map (Arbnum.toString o numSyntax.dest_numeral) ns) ^ "\n")
  end) (fst(listSyntax.dest_list(rhs(concl edges))));
val _ = TextIO.closeOut stream;
