(* The fixed baseline meets CakeML's saved-PC and FFI-entry layout contract. *)
Theory initBaselineStartPc
Ancestors initBaselineAdmission initCompilerMachine initFfiBoundary
Libs preamble cv_transLib
open targetSemTheory initMachineTheory initSubmissionTheory
  initCompilerMachineTheory initArtifactsTheory initCompiledMetadataTheory
  initBootstrapTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
Theorem baseline_ffi_boundary:
  mmio_pcs_min_index compiledFfiNames = SOME compiledFirst
Proof
  irule ffi_boundary_exact >>
  mp_tac baseline_admitted >> rewrite_tac [admitted_def] >> strip_tac >>
  fs [baselineSubmission_def]
QED
val names_literal = cv_eval ``compiledFfiNames``;
val extra_literal = cv_eval ``baselineExtra``;
val bounded_rewrite = CONV_RULE
  (DEPTH_CONV (FIRST_CONV (map HO_REWR_CONV
    [bounded_all_guard,bounded_all,member_all])) THENC DEPTH_CONV BETA_CONV);
val start_layout = REWRITE_CONV
  [start_pc_ok_def,compilerMachineConfig_def,submissionConfig_def,
   baselineSubmission_def,challengeMachineConfig_def]
  ``start_pc_ok (compilerMachineConfig baselineSubmission) (n2w baselineNativePc)``
  |> SIMP_RULE (srw_ss()) [baseline_ffi_boundary,IN_DEF,programDomain_def,
       submissionMemoryDomain_def,submissionSharedDomain_def]
  |> REWRITE_RULE [names_literal,extra_literal,compiled_first]
  |> bounded_rewrite;
Theorem baseline_start_pc:
  start_pc_ok (compilerMachineConfig baselineSubmission) (n2w baselineNativePc)
Proof
  CONV_TAC (K (TRANS start_layout (EVAL (rhs (concl start_layout))))) >>
  CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_EXISTS_CONV EVAL)) >> EVAL_TAC
QED
val _ = if null(hyp baseline_start_pc) then ignore(check_thm baseline_start_pc)
  else failwith "baseline start PC assumptions";
val _ = if null(hyp baseline_ffi_boundary) then ignore(check_thm baseline_ffi_boundary)
  else failwith "baseline FFI boundary assumptions";
