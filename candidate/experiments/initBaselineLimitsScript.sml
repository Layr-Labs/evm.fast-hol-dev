(* Discharge the concrete stack resource condition at baseline native entry. *)
Theory initBaselineLimits
Ancestors initStackLimit initBaselineInstalled initBackendConfig
Libs preamble wordsLib
open asmPropsTheory targetSemTheory wordsTheory initMachineTheory
  initSubmissionTheory initCompilerMachineTheory initBaselineInitialTheory
  initCompilationInputTheory backendTheory riscv_targetTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = metisTools.limit := {time=SOME 10.0,infs=NONE};
Theorem baseline_native_registers:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms ==>
  ms.c_gpr ms.procID 11w = 0xa1000000w /\
  ms.c_gpr ms.procID 12w = 0x7df000000w /\
  ms.c_gpr ms.procID 13w = 0x7e0000000w
Proof
  strip_tac >>
  `ms.c_gpr ms.procID 11w = (bootFinalState (baselineInitialAsm input)).regs 11 /\
   ms.c_gpr ms.procID 12w = (bootFinalState (baselineInitialAsm input)).regs 12 /\
   ms.c_gpr ms.procID 13w = (bootFinalState (baselineInitialAsm input)).regs 13` by
    (fs [target_state_rel_def,restrictedTarget_def,riscv_target_def,riscv_config_def] >>
     metis_tac []) >> simp [baseline_native_entry]
QED
Theorem baseline_stack_limit_sufficient:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms ==>
  7480 < FST (backendProof$read_limits riscv_config
    (set_oracle guestConfig allocation) (compilerMachineConfig baselineSubmission) ms)
Proof
  strip_tac >> drule baseline_native_registers >> strip_tac >>
  simp [backendProofTheory.read_limits_def,compilerMachineConfig_def,
        submissionConfig_def,challengeMachineConfig_def,restrictedTarget_def,
        riscv_target_def,set_oracle_def,guestConfig_def,pancakeRiscvConfig_def] >>
  EVAL_TAC >> fs [] >> EVAL_TAC
QED
Theorem baseline_bounded_compilation:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms ==>
  ?c depth.
    pan_to_targetProof$compile_prog_max (set_oracle guestConfig allocation)
      (compilerMachineConfig baselineSubmission) prepared_guest =
      (SOME (compiledBytes,compiledBitmaps,c),SOME depth) /\
    c.lab_conf = compiledConfig.lab_conf /\
    pan_to_targetProof$option_lt (SOME depth)
      (SOME (FST (backendProof$read_limits riscv_config
        (set_oracle guestConfig allocation) (compilerMachineConfig baselineSubmission) ms)))
Proof
  strip_tac >>
  `(compilerMachineConfig baselineSubmission).target.config = riscv_config` by
    simp [compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
          restrictedTarget_def,riscv_target_def] >>
  drule initStackLimitTheory.guest_bounded_compilation >> strip_tac >>
  qexists_tac `c` >> qexists_tac `depth` >>
  imp_res_tac baseline_stack_limit_sufficient >>
  fs [pan_to_targetProofTheory.option_lt_def] >> intLib.ARITH_TAC
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline resource assumptions")
  [baseline_native_registers,baseline_stack_limit_sufficient,baseline_bounded_compilation];
