(* Full Pancake installation witness for the fixed baseline native entry. *)
Theory initBaselineInstalled
Ancestors initBaselineGoodInit initBaselineMemoryHeaders initBaselineMmioLayout
          initBaselineBitmapInstalled pan_to_targetProof
Libs preamble wordsLib
open wordsTheory alignmentTheory asmPropsTheory targetSemTheory miscTheory
  initParamsTheory initSourceTheory initSubmissionTheory initMachineTheory
  initCompilerMachineTheory initBaselineAdmissionTheory initBaselineInitialTheory
  initBaselineConfiguredTheory initDataDomainTheory initBitmapDomainTheory
  initBootstrapTheory initArtifactsTheory initBytecodeTheory
  initBaselinePackedMemoryTheory initInstallationMetadataTheory
  initBaselineStartPcTheory riscv_targetTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_heap_stack_domain:
  {w:word64 | (bootFinalState (baselineInitialAsm input)).regs 11 <=+ w /\
               w <+ (bootFinalState (baselineInitialAsm input)).regs 13} = heapStackDomain
Proof
  simp [EXTENSION,heapStackDomain_def,baseline_native_entry,WORD_LS,WORD_LO,
        sourceBase_def,ramEnd_def,ramStart_def,ramSize_def]
QED
Theorem baseline_shared_word_domain:
  sharedDomain = submissionSharedDomain INTER byte_aligned
Proof
  simp [EXTENSION,IN_DEF,sharedDomain_def,submissionSharedDomain_def,
        byte_align_aligned] >> metis_tac []
QED
Theorem baseline_pan_installed:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms ==>
  pan_installed compiledBytes 760 compiledBitmaps 0 compiledConfig.lab_conf.ffi_names
    (11,13) (compilerMachineConfig baselineSubmission) compiledConfig.lab_conf.shmem_extra ms
    (crep_to_loopProof$wlab_wloc o sourceMemory) ordinaryDomain sharedDomain
Proof
  strip_tac >> drule baseline_good_init_state >> strip_tac >>
  `((compilerMachineConfig baselineSubmission).target.get_pc ms) = n2w baselineNativePc` by
    (fs [compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
         target_state_rel_def,restrictedTarget_def,riscv_target_def] >>
     metis_tac [baseline_native_entry]) >>
  rewrite_tac [pan_installed_def,compiled_installation_names,compiled_installation_mmio] >>
  qexists_tac `bootFinalState (baselineInitialAsm input)` >>
  qexists_tac `baselinePackedMemory input` >>
  qexists_tac `n2w (bootDataRam+24):word64` >>
  qexists_tac `bitmapDomain` >> qexists_tac `submissionSharedDomain` >>
  simp [LET_THM,baseline_heap_stack_domain,baseline_shared_word_domain,
        baseline_packed_source_memory,o_DEF,data_domains_disjoint] >>
  mp_tac baseline_installation_headers >> mp_tac baseline_bitmap_allocation >>
  mp_tac baseline_mmio_layout >>
  simp [baseline_native_entry,bytes_in_word_def,dimindex_64,
        byte_aligned_def,aligned_w2n,WORD_LS,WORD_LO,
        sourceBase_def,ramEnd_def,ramStart_def,ramSize_def,
        bootDataRam_def,bootDataEnd_def,compiled_bitmap_count,compiled_byte_count,
        baselineNativePc_def] >>
  rpt strip_tac >>
  fs [compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
      baselineSubmission_def,baseline_ffi_boundary]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline Pancake installation assumptions")
  [baseline_heap_stack_domain,baseline_shared_word_domain,baseline_pan_installed];
