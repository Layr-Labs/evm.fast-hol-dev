(* A compact, checked ranking certificate for the word compiler's call graph.
   The ranking is untrusted data; every direct call must lower its rank. *)
Theory initStackRank
Ancestors word_depthProof
Libs preamble
open word_depthTheory word_depthProofTheory wordLangTheory sptreeTheory;
val _ = metisTools.limit := {time=SOME 5.0,infs=NONE};
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition stackRank_def:
  stackRank (ranks:num num_map) n = case lookup n ranks of NONE => 0 | SOME r => r
End
Definition rankedCalls_def:
  (rankedCalls ranks (code:(num # 'a wordLang$prog) num_map) n
     (wordLang$Seq p q:'a wordLang$prog) =
     (rankedCalls ranks code n p /\ rankedCalls ranks code n q)) /\
  (rankedCalls ranks code n (wordLang$If _ _ _ p q) =
     (rankedCalls ranks code n p /\ rankedCalls ranks code n q)) /\
  (rankedCalls ranks code n (wordLang$Call ret dest args handler) =
     case dest of NONE => F | SOME d =>
       stackRank ranks d < stackRank ranks n /\ IS_SOME (lookup d code) /\
       (case ret of NONE => T | SOME (_,_,p,_,_) => rankedCalls ranks code n p) /\
       (case handler of NONE => T | SOME (_,p,_,_) => rankedCalls ranks code n p)) /\
  (rankedCalls ranks code n (wordLang$MustTerminate p) = rankedCalls ranks code n p) /\
  (rankedCalls ranks code n (wordLang$Loop _ p _) = rankedCalls ranks code n p) /\
  (rankedCalls ranks code n (wordLang$Install _ _ _ _ _ _) = F) /\
  (rankedCalls ranks code n _ = T)
Termination
  WF_REL_TAC `measure (\(ranks,code,n,p). prog_size (K 0) p)` >>
  rw [] >> simp [wordLangTheory.prog_size_def]
End
Definition stackBound_def:
  stackBound (result:num option) (bound:num) <=> ?value. result = SOME value /\ value <= bound
End
Theorem stackBound_zero[simp]:
  stackBound (SOME 0) bound
Proof
  simp [stackBound_def]
QED
Theorem stackBound_weaken:
  stackBound result a /\ a <= b ==> stackBound result b
Proof
  rw [stackBound_def] >> simp [] >> intLib.ARITH_TAC
QED
Theorem stackBound_max:
  stackBound x bound /\ stackBound y bound ==>
  stackBound (OPTION_MAP2 MAX x y) bound
Proof
  rw [stackBound_def] >> simp [MAX_DEF]
QED
Theorem stackBound_frame:
  lookup n sizes = SOME f /\ f <= 92 /\ stackBound result bound ==>
  stackBound (OPTION_MAP2 (+) (lookup n sizes) result) (bound + 92)
Proof
  rw [stackBound_def] >> simp [] >> intLib.ARITH_TAC
QED
Theorem stackBound_handler:
  stackBound result bound ==>
  stackBound (OPTION_MAP ((+) 3) result) (bound + 3)
Proof
  rw [stackBound_def] >> simp []
QED
Theorem stackRank_agree_delete:
  (!i. stackRank ranks i < stackRank ranks n ==> lookup i funs = lookup i code) /\
  stackRank ranks d < stackRank ranks n ==>
  (!i. stackRank ranks i < stackRank ranks d ==> lookup i (delete d funs) = lookup i code)
Proof
  rw [lookup_delete] >>
  `i <> d` by (strip_tac >> fs []) >> simp [] >>
  first_x_assum irule >> intLib.ARITH_TAC
QED
Theorem stackRank_agree_lower:
  (!i. stackRank ranks i < stackRank ranks n ==> lookup i funs = lookup i code) /\
  stackRank ranks d < stackRank ranks n ==>
  (!i. stackRank ranks i < stackRank ranks d ==> lookup i funs = lookup i code)
Proof
  rw [] >> first_x_assum irule >> intLib.ARITH_TAC
QED

Theorem call_graph_rank_bound:
  !ranks (code:(num # 'a wordLang$prog) num_map) sizes.
    (!i a body. lookup i code = SOME (a,body) ==>
       rankedCalls ranks code i body) /\
    (!i. IS_SOME (lookup i code) ==>
       ?f. lookup i sizes = SOME f /\ f <= 92) ==>
    !funs n ns total p.
      IS_SOME (lookup n code) /\
      (!i. stackRank ranks i < stackRank ranks n ==>
         lookup i funs = lookup i code) /\
      rankedCalls ranks code n p ==>
      stackBound (max_depth sizes (call_graph funs n ns total p))
        ((stackRank ranks n + 1) * 187)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac call_graph_ind >> rpt strip_tac >>
  fs [rankedCalls_def] >> once_rewrite_tac [call_graph_def] >>
  fs [rankedCalls_def,max_depth_def,max_depth_mk_Branch] >>
  TRY (metis_tac [stackBound_max,stackBound_zero])
  >- (Cases_on `dest` >> gvs [] >>
      rename1 `stackRank ranks d < stackRank ranks n` >>
      `lookup d funs = lookup d code` by metis_tac [] >>
      Cases_on `lookup d code` >> fs [] >>
      rename1 `lookup d code = SOME pair` >> PairCases_on `pair` >> fs [] >>
      Cases_on `ret` >> fs []
      >- (`?fdd. lookup d sizes = SOME fdd /\ fdd <= 92` by
            (first_x_assum (mp_tac o Q.SPEC `d`) >> simp []) >>
          rpt IF_CASES_TAC >>
          fs [max_depth_mk_Branch,max_depth_def,stackBound_def,MAX_DEF] >>
          intLib.ARITH_TAC) >>
      `!i. stackRank ranks i < stackRank ranks d ==>
           lookup i (delete d funs) = lookup i code` by
        metis_tac [stackRank_agree_delete] >>
      `?fnn. lookup n sizes = SOME fnn /\ fnn <= 92` by
        (first_x_assum (mp_tac o Q.SPEC `n`) >> simp []) >>
      `?fdd. lookup d sizes = SOME fdd /\ fdd <= 92` by
        (first_x_assum (mp_tac o Q.SPEC `d`) >> simp []) >>
      PairCases_on `x` >> Cases_on `handler` >> fs []
      >- (fs [max_depth_mk_Branch,max_depth_def,stackBound_def,MAX_DEF] >>
          rw [] >> intLib.ARITH_TAC) >>
      PairCases_on `x` >>
      fs [max_depth_mk_Branch,max_depth_def,stackBound_def,MAX_DEF] >>
      rw [] >> intLib.ARITH_TAC) >>
  `?fnn. lookup n sizes = SOME fnn /\ fnn <= 92` by metis_tac [] >>
  fs [stackBound_def] >> intLib.ARITH_TAC
QED

Theorem full_call_graph_rank_bound:
  (!i a body. lookup i code = SOME (a,body) ==>
     rankedCalls ranks code i body) /\
  (!i. IS_SOME (lookup i code) ==>
     ?f. lookup i sizes = SOME f /\ f <= 92) /\
  IS_SOME (lookup n code) ==>
  stackBound (max_depth sizes (full_call_graph n code))
    ((stackRank ranks n + 1) * 187)
Proof
  rpt strip_tac >> Cases_on `lookup n code` >> fs [] >>
  PairCases_on `x` >> fs [full_call_graph_def,max_depth_def] >>
  `stackBound (max_depth sizes (call_graph code n [n] (size code) x1))
     ((stackRank ranks n + 1) * 187)` by
    (irule call_graph_rank_bound >> qexists_tac `code` >> simp [] >>
     metis_tac []) >>
  `?f. lookup n sizes = SOME f /\ f <= 92` by
    (first_x_assum (mp_tac o Q.SPEC `n`) >> simp []) >>
  fs [stackBound_def,MAX_DEF] >> rw [] >> intLib.ARITH_TAC
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "stack ranking theorem has assumptions")
  [call_graph_rank_bound,full_call_graph_rank_bound];

Definition checkedRanks_def:
  checkedRanks ranks (code:(num # 'a wordLang$prog) num_map) (sizes:num num_map) <=>
    EVERY (\(n,a,p). rankedCalls ranks code n p /\
      case lookup n sizes of NONE => F | SOME f => f <= 92) (toAList code)
End
Theorem checkedRanks_sound:
  checkedRanks ranks code sizes ==>
  (!i a body. lookup i code = SOME (a,body) ==>
    rankedCalls ranks code i body) /\
  (!i. IS_SOME (lookup i code) ==>
    ?f. lookup i sizes = SOME f /\ f <= 92)
Proof
  rw [checkedRanks_def,listTheory.EVERY_MEM,pairTheory.FORALL_PROD,MEM_toAList] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  fs [optionTheory.IS_SOME_EXISTS] >> rpt strip_tac >>
  TRY (metis_tac []) >> Cases_on `x` >> res_tac >>
  Cases_on `lookup i sizes` >> fs []
QED
Theorem checkedRanks_bound:
  checkedRanks ranks code sizes /\ IS_SOME (lookup n code) ==>
  stackBound (max_depth sizes (full_call_graph n code))
    ((stackRank ranks n + 1) * 187)
Proof
  metis_tac [checkedRanks_sound,full_call_graph_rank_bound]
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "stack checker theorem has assumptions")
  [checkedRanks_sound,checkedRanks_bound];
