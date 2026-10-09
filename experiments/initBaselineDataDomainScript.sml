(* Ordinary data allocation lies in the fixed baseline program memory. *)
Theory initBaselineDataDomain
Ancestors initDataDomain initBaselineConfigured
Libs preamble wordsLib
open wordsTheory initParamsTheory initBootstrapTheory initSubmissionTheory
  initBaselineAdmissionTheory initCompiledMetadataTheory
  initBitmapDomainTheory initMachineTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_data_domain:
  heapStackDomain UNION bitmapDomain SUBSET programDomain baselineSubmission
Proof
  rewrite_tac [SUBSET_DEF] >> qx_gen_tac `a` >> Cases_on `a` >>
  rw [IN_DEF,heapStackDomain_def,bitmapDomain_def,
      programDomain_def,submissionMemoryDomain_def,submissionSharedDomain_def,
      baselineSubmission_def,compiled_first,baselineNativePc_def,
      bootDataRam_def,bootDataEnd_def,ffiOffset_def,initialPc_def,
      codeSizeLimit_def,ramStart_def,ramEnd_def,ramSize_def,sourceBase_def,
      inputStart_def,inputEnd_def,inputSize_def,outputStart_def,
      outputEnd_def,outputSize_def,WORD_EQ_SUB_LADD,word_add_n2w,n2w_11,
      w2n_n2w,dimword_64] >> decide_tac
QED
Theorem baseline_data_domain_installed:
  heapStackDomain UNION bitmapDomain SUBSET
    (bootFinalState (baselineInitialAsm input)).mem_domain
Proof
  rewrite_tac [baseline_native_constants] >>
  ACCEPT_TAC baseline_data_domain
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline data domain assumptions")
  [baseline_data_domain,baseline_data_domain_installed];
