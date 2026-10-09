(* Code and code-buffer placement for the fixed native image. *)
Theory initBaselineCodeMemory
Ancestors initBaselineDataDomain initCodeMemory
Libs preamble wordsLib
open wordsTheory miscTheory asmPropsTheory targetSemTheory initParamsTheory
  initBytecodeTheory initBootstrapTheory initSubmissionTheory initMachineTheory
  initCompilerMachineTheory initBaselineInitialTheory initBaselineConfiguredTheory
  initDataDomainTheory initBitmapDomainTheory initBaselineAdmissionTheory
  initCompiledMetadataTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_native_bytes_separated:
  bytes_in_mem (bootFinalState (baselineInitialAsm input)).pc compiledBytes
    (bootFinalState (baselineInitialAsm input)).mem
    (bootFinalState (baselineInitialAsm input)).mem_domain
    (heapStackDomain UNION bitmapDomain)
Proof
  rewrite_tac [baseline_native_entry] >> irule installed_bytes_separated >>
  conj_tac
  >- (rw [IN_DEF,heapStackDomain_def,bitmapDomain_def,compiled_byte_count,
          word_add_n2w,baselineNativePc_def,sourceBase_def,bootDataRam_def,
          bootDataEnd_def,w2n_n2w,dimword_64] >> decide_tac) >>
  ACCEPT_TAC baseline_native_installed
QED
Theorem baseline_code_buffer_domain:
  n < 760 ==>
  n2w (n+LENGTH compiledBytes) + n2w baselineNativePc IN programDomain baselineSubmission /\
  n2w (n+LENGTH compiledBytes) + n2w baselineNativePc NOTIN
    heapStackDomain UNION bitmapDomain
Proof
  strip_tac >> conj_tac
  >- (simp_tac std_ss [word_add_n2w,IN_DEF] >>
      irule initInitialCodeTheory.program_domain_above_anchor >>
      simp [baselineSubmission_def,compiled_first,compiled_byte_count,
            initialPc_def,codeSizeLimit_def,baselineNativePc_def,ffiOffset_def] >>
      decide_tac) >>
  rw [IN_DEF,heapStackDomain_def,bitmapDomain_def,compiled_byte_count,
      word_add_n2w,baselineNativePc_def,sourceBase_def,bootDataRam_def,
      bootDataEnd_def,w2n_n2w,dimword_64] >> decide_tac
QED
Theorem baseline_code_buffer_installed:
  n < 760 ==>
  n2w (n+LENGTH compiledBytes) + (bootFinalState (baselineInitialAsm input)).pc IN
    (bootFinalState (baselineInitialAsm input)).mem_domain /\
  n2w (n+LENGTH compiledBytes) + (bootFinalState (baselineInitialAsm input)).pc NOTIN
    heapStackDomain UNION bitmapDomain
Proof
  rewrite_tac [baseline_native_entry,baseline_native_constants] >>
  ACCEPT_TAC baseline_code_buffer_domain
QED
Theorem baseline_native_code_loaded:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms ==>
  code_loaded compiledBytes (compilerMachineConfig baselineSubmission) ms
Proof
  strip_tac >> irule installed_code_loaded >>
  qexists_tac `bootFinalState (baselineInitialAsm input)` >>
  simp [compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
        baseline_native_constants,baseline_native_entry] >>
  metis_tac [baseline_native_constants,baseline_native_installed]
QED
Theorem baseline_code_buffer_nonwrapping:
  760 + LENGTH compiledBytes < dimword (:64)
Proof
  simp [compiled_byte_count,dimword_64]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline code memory assumptions")
  [baseline_native_bytes_separated,baseline_code_buffer_domain,
   baseline_code_buffer_installed,baseline_native_code_loaded,
   baseline_code_buffer_nonwrapping];
