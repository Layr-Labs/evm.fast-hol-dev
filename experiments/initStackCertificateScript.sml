(* Validate the untrusted rank data against the exact optimized word program. *)
Theory initStackCertificate
Ancestors initStackFrames initStackRank initStackRanksData
Libs preamble cv_transLib
open initStackRankTheory initStackFramesTheory initStackRanksDataTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th = if null(hyp th) then save_thm(name,check_thm th)
  else failwith (name ^ " has assumptions");
val _ = cv_auto_trans stackRank_def;
val _ = cv_auto_trans (INST_TYPE [alpha |-> ``:64``] rankedCalls_def);
val _ = cv_auto_trans (INST_TYPE [alpha |-> ``:64``] checkedRanks_def);
val _ = cv_auto_trans optimized_ranks_def;
Definition optimized_code_def:
  optimized_code = fromAList optimized_word
End
val _ = cv_auto_trans optimized_code_def;
val optimized_ranks_checked = save_closed "optimized_ranks_checked"
  (EQT_ELIM (cv_eval ``checkedRanks optimized_ranks optimized_code optimized_frames``));
val optimized_entry_present = save_closed "optimized_entry_present"
  (EQT_ELIM (cv_eval ``IS_SOME (lookup 64 optimized_code)``));
val optimized_entry_rank = save_closed "optimized_entry_rank"
  (cv_eval ``stackRank optimized_ranks 64``);
Theorem optimized_stack_bound:
  ?depth. word_depth$max_depth optimized_frames
    (word_depth$full_call_graph 64 optimized_code) = SOME depth /\ depth <= 7480
Proof
  mp_tac (MATCH_MP checkedRanks_bound
    (CONJ optimized_ranks_checked optimized_entry_present)) >>
  simp [stackBound_def,optimized_entry_rank]
QED
val _ = save_closed "checked_optimized_stack_bound" optimized_stack_bound;
