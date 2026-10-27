(* Compose normal-instruction simulation for a machine with no interference. *)
Theory initChallengeExecution
Ancestors initChallengeStep
Libs preamble wordsLib
open asmSemTheory asmPropsTheory targetSemTheory targetPropsTheory
  initMachineTheory initChallengeStepTheory relationTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition identityNextInterference_def:
  identityNextInterference (mc:(64,riscv_state,'c) machine_config) <=>
    !n ms. mc.next_interfer n ms = ms
End
Definition challengeAsmEdge_def:
  challengeAsmEdge (mc:(64,riscv_state,'c) machine_config) s1 s2 <=>
    ?instruction. asm_step mc.target.config s1 instruction s2 /\
      mc.prog_addresses = s1.mem_domain /\
      ffi_entry_pcs_disjoint mc s1
        (LENGTH (mc.target.config.encode instruction))
End
Theorem identity_shift_interfer:
  identityNextInterference mc ==> shift_interfer n mc = mc
Proof
  rw [identityNextInterference_def,shift_interfer_def] >>
  `misc$shift_seq n mc.next_interfer = mc.next_interfer` by
    simp [FUN_EQ_THM,miscTheory.shift_seq_def] >>
  simp []
QED
Theorem challenge_identity_interference:
  identityNextInterference
    (challengeMachineConfig pc program shared names nexternal extra)
Proof
  simp [identityNextInterference_def,challengeMachineConfig_def]
QED
Theorem challenge_edge_execution:
  encoder_correct mc.target /\ identityNextInterference mc /\
  challengeAsmEdge mc s1 s2 /\ target_state_rel mc.target s1 ms1 ==>
  ?n ms2.
    (!k. challengeEvaluate mc io (k+n) ms1 = challengeEvaluate mc io k ms2) /\
    target_state_rel mc.target s2 ms2 /\ n <> 0
Proof
  rw [challengeAsmEdge_def] >>
  `s2 = asm instruction (s1.pc + n2w (LENGTH (mc.target.config.encode instruction))) s1` by
    fs [asm_step_def] >>
  gvs [] >>
  `interference_ok mc.next_interfer (mc.target.proj s1.mem_domain)` by
    fs [interference_ok_def,identityNextInterference_def] >>
  Q.ISPECL_THEN [`mc`,`s1`,`ms1`,`io`,`instruction`] mp_tac
    (SIMP_RULE (srw_ss()) [] asm_step_IMP_challenge_step) >>
  simp [] >> strip_tac >>
  qexists_tac `l` >> qexists_tac `ms2` >>
  fs [identity_shift_interfer] >> metis_tac []
QED
Theorem challenge_rtc_execution:
  encoder_correct mc.target /\ identityNextInterference mc ==>
  !s1 s2. RTC (challengeAsmEdge mc) s1 s2 ==>
  !ms1 io. target_state_rel mc.target s1 ms1 ==>
  ?n ms2.
    (!k. challengeEvaluate mc io (k+n) ms1 = challengeEvaluate mc io k ms2) /\
    target_state_rel mc.target s2 ms2
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- (qexists_tac `0` >> qexists_tac `ms1` >> simp []) >>
  drule_all challenge_edge_execution >>
  disch_then (qspec_then `io` strip_assume_tac) >>
  first_x_assum (qspecl_then [`ms2`,`io`] mp_tac) >> simp [] >> strip_tac >>
  qexists_tac `n+n'` >> qexists_tac `ms2'` >> simp [] >>
  metis_tac [ADD_ASSOC,ADD_COMM]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "challenge trace composition assumptions")
  [identity_shift_interfer,challenge_identity_interference,
   challenge_edge_execution,challenge_rtc_execution];
