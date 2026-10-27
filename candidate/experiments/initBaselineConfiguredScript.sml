(* The concrete native-entry assembler state has the compiler's target setup. *)
Theory initBaselineConfigured
Ancestors initBaselineInitial initCompilerMachine
Libs preamble wordsLib
open wordsTheory asmPropsTheory targetSemTheory initMachineTheory
  initSubmissionTheory initCompilerMachineTheory initBaselineInitialTheory
  riscv_targetTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_native_constants:
  (bootFinalState (baselineInitialAsm input)).mem_domain = programDomain baselineSubmission /\
  (bootFinalState (baselineInitialAsm input)).lr = 1 /\
  (bootFinalState (baselineInitialAsm input)).align = 2 /\
  ~(bootFinalState (baselineInitialAsm input)).be
Proof
  mp_tac (MATCH_MP RTC_asm_step_consts baseline_bootstrap_execution) >>
  simp [baselineInitialAsm_def]
QED
Theorem baseline_native_configured:
  target_configured (bootFinalState (baselineInitialAsm input))
    (compilerMachineConfig baselineSubmission)
Proof
  simp [target_configured_def,baseline_native_constants,baseline_native_entry,
        compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
        restrictedTarget_def,riscv_target_def,riscv_config_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "native target configuration assumptions")
  [baseline_native_constants,baseline_native_configured];
