(* Lift the concrete bootstrap trace to the challenge's restricted CPU. *)
Theory initBaselineRestrictedExecution
Ancestors initBaselineInitial initRestrictedEncoder initEncoderExecution
Libs preamble wordsLib
open wordsTheory initBootstrapTheory initBaselineInitialTheory initBaselineAdmissionTheory initSubmissionTheory
  initMachineTheory initBootstrapStateTheory initRestrictedStepTheory
  initRestrictedEncoderTheory initEncoderExecutionTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem restricted_target_config:
  restrictedTarget.config = riscv_config
Proof
  simp [restrictedTarget_def,riscv_targetTheory.riscv_target_def]
QED
Theorem baseline_restricted_execution:
  ?final.
    RTC (\s s'. s' = restrictedTarget.next s)
      (initialState baselineSubmission input) final /\
    target_state_rel restrictedTarget
      (bootFinalState (baselineInitialAsm input)) final
Proof
  mp_tac (MATCH_MP encoder_rtc_reaches restricted_encoder_correct) >>
  disch_then (qspecl_then
    [`baselineInitialAsm input`,`bootFinalState (baselineInitialAsm input)`] mp_tac) >>
  simp [restricted_target_config,baseline_bootstrap_execution,
        restricted_target_state_relation] >>
  disch_then (qspec_then `initialState baselineSubmission input` mp_tac) >>
  simp [baseline_initial_target_relation]
QED
Theorem baseline_restricted_native_entry:
  ?final.
    RTC (\s s'. s' = restrictedTarget.next s)
      (initialState baselineSubmission input) final /\
    riscv_ok final /\ final.c_PC final.procID = n2w baselineNativePc /\
    final.c_gpr final.procID 10w = n2w baselineNativePc /\
    final.c_gpr final.procID 11w = 0xa1000000w /\
    final.c_gpr final.procID 12w = 0x7df000000w /\
    final.c_gpr final.procID 13w = 0x7e0000000w /\
    bytes_in_memory (n2w baselineNativePc) initBytecode$compiledBytes
      final.MEM8 (programDomain baselineSubmission)
Proof
  strip_assume_tac baseline_restricted_execution >>
  qexists_tac `final` >>
  fs [restricted_target_state_relation,asmPropsTheory.target_state_rel_def,
      riscv_targetTheory.riscv_target_def,riscv_targetTheory.riscv_config_def] >>
  simp [baseline_native_entry] >>
  `(bootFinalState (baselineInitialAsm input)).mem_domain =
    programDomain baselineSubmission` by
    (mp_tac (Q.INST [`s` |-> `baselineInitialAsm input`]
       initBootstrapFrameTheory.bootstrap_preserves_domain) >>
     simp [baselineInitialAsm_def]) >>
  irule miscTheory.bytes_in_memory_change_mem >>
  qexists_tac `(bootFinalState (baselineInitialAsm input)).mem` >>
  conj_tac
  >- metis_tac [baseline_native_installed,miscTheory.bytes_in_memory_in_domain] >>
  metis_tac [baseline_native_installed]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline restricted execution assumptions")
  [baseline_restricted_execution,baseline_restricted_native_entry];
