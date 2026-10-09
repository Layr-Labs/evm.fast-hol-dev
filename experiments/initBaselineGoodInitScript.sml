(* Assemble the full native-entry machine initialization contract. *)
Theory initBaselineGoodInit
Ancestors initBaselineCodeMemory initBaselineStartPc initSharedDomain
          initBaselinePackedMemory
Libs preamble wordsLib
open wordsTheory targetSemTheory asmPropsTheory initCompilerMachineTheory
  initSubmissionTheory initMachineTheory initBaselineAdmissionTheory
  initBaselineInitialTheory initBaselineConfiguredTheory initBaselineDataDomainTheory
  initDataDomainTheory initBootstrapTheory initBytecodeTheory riscv_targetTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_good_init_state:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms ==>
  good_init_state (compilerMachineConfig baselineSubmission) ms compiledBytes 760
    (bootFinalState (baselineInitialAsm input)) (baselinePackedMemory input)
    (heapStackDomain UNION bitmapDomain) submissionSharedDomain
Proof
  strip_tac >> drule baseline_native_code_loaded >> strip_tac >>
  simp [good_init_state_def,baseline_native_configured,
        compiler_ffi_interference,baseline_admitted,compiler_install_interference,
        compiler_identity_interference,baseline_native_code_loaded,
        baseline_native_bytes_separated,baseline_data_domain_installed,
        data_domain_align_closed,shared_domain_align_closed,
        baseline_code_buffer_installed,baseline_code_buffer_nonwrapping] >>
  simp [baseline_native_entry,baseline_native_constants,baseline_start_pc] >>
  fs [compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
      target_state_rel_def,restrictedTarget_def,riscv_target_def,riscv_config_def,
      program_shared_disjoint,baseline_packed_byte_memory,baseline_native_entry,
      baselineNativePc_def] >>
  simp []
QED
val _ = if null(hyp baseline_good_init_state)
  then ignore(check_thm baseline_good_init_state)
  else failwith "baseline initialization assumptions";
