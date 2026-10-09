(* Exact fixed MMIO addresses and metadata for the compiler installation. *)
Theory initBaselineMmioLayout
Ancestors initInstallationMetadata initBaselineAdmission initCompilerMachine
Libs preamble cv_transLib
open wordsTheory targetSemTheory initMachineTheory initSubmissionTheory
  initCompilerMachineTheory initBootstrapTheory initBytecodeTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
Definition baselineCompilerMmioLayout_def:
  baselineCompilerMmioLayout =
  (MAP (\r:lab_to_target$shmem_info_num. baselineNativePc+r.entry_pc) compiledMmio =
    DROP compiledFirst (MAP w2n (compilerMachineConfig baselineSubmission).ffi_entry_pcs) /\
   (compilerMachineConfig baselineSubmission).mmio_info =
    ZIP (GENLIST (\i. i+compiledFirst) (LENGTH compiledMmio),
      MAP (\r:lab_to_target$shmem_info_num.
        (r.nbytes,Addr r.addr_reg r.addr_off,r.reg,n2w r.exit_pc+n2w baselineNativePc))
        compiledMmio) /\
   760 + LENGTH compiledBytes + lab_to_target$ffi_offset*(compiledFirst+3) < dimword (:64))
End
val layout_def = SIMP_RULE (srw_ss())
  [compilerMachineConfig_def,submissionConfig_def,baselineSubmission_def,
   challengeMachineConfig_def,compiled_byte_count,dimword_64]
  baselineCompilerMmioLayout_def;
val _ = cv_auto_trans layout_def;
val layout_checked = EQT_ELIM (cv_eval ``baselineCompilerMmioLayout``);
val baseline_mmio_layout = REWRITE_RULE [baselineCompilerMmioLayout_def] layout_checked;
val _ = if null(hyp baseline_mmio_layout) then
  save_thm ("baseline_mmio_layout",check_thm baseline_mmio_layout)
  else failwith "baseline MMIO layout assumptions";
