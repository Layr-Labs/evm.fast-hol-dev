(* Bootstrap steps with the challenge evaluator's domain/FFI side conditions. *)
Theory initBootstrapChallengeStep
Ancestors initBootstrapFfi initBootstrapStep initChallengeExecution
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapStepTheory
  initBootstrapFfiTheory initChallengeExecutionTheory initSubmissionTheory
  initMachineTheory initBaselineAdmissionTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition challengeBootSteps_def:
  challengeBootSteps [] (s:64 asm_state) = T /\
  challengeBootSteps (instruction::rest) s =
    (challengeAsmEdge (submissionConfig baselineSubmission)
      s (bootAfter instruction s) /\
     challengeBootSteps rest (bootAfter instruction s))
End
Theorem bootstrap_challenge_step:
  MEM (pc,instruction) bootstrapBlocks /\ bootstrapRomInvariant input s /\
  s.pc = n2w pc /\ s.lr = 1 /\ ~s.be /\ s.align = 2 /\
  ~(bootAfter instruction s).failed ==>
  challengeAsmEdge (submissionConfig baselineSubmission) s (bootAfter instruction s)
Proof
  strip_tac >>
  `(submissionConfig baselineSubmission).target.config = riscv_config` by
    simp [submissionConfig_def,challengeMachineConfig_def,restrictedTarget_def,
      riscv_targetTheory.riscv_target_def] >>
  `(submissionConfig baselineSubmission).prog_addresses = s.mem_domain` by
    fs [submissionConfig_def,challengeMachineConfig_def,bootstrapRomInvariant_def] >>
  simp [challengeAsmEdge_def] >> qexists_tac `instruction` >> simp [] >> conj_tac
  >- (irule bootstrap_asm_step >> fs [] >> metis_tac []) >>
  simp [riscv_targetTheory.riscv_config_def] >>
  irule bootstrap_instruction_ffi_disjoint >> fs [] >> metis_tac []
QED
Theorem challengeBootSteps_append:
  !xs ys s. challengeBootSteps (xs ++ ys) s <=>
    challengeBootSteps xs s /\ challengeBootSteps ys (bootRun xs s)
Proof
  Induct >> simp [challengeBootSteps_def,initBootstrapLoopTheory.bootRun_def] >>
  metis_tac []
QED
Theorem challengeBootSteps_RTC:
  !xs s. challengeBootSteps xs s ==>
    RTC (challengeAsmEdge (submissionConfig baselineSubmission)) s (bootRun xs s)
Proof
  Induct >> rw [challengeBootSteps_def,initBootstrapLoopTheory.bootRun_def] >>
  irule relationTheory.RTC_TRANS >> qexists_tac `bootAfter h s` >> conj_tac
  >- (irule relationTheory.RTC_SINGLE >> metis_tac []) >>
  first_x_assum irule >> fs []
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "bootstrap challenge-step assumptions")
  [bootstrap_challenge_step,challengeBootSteps_append,challengeBootSteps_RTC];
