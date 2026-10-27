(* Fetchable bootstrap bytes in the admitted baseline's initial memory. *)
Theory initBootstrapInstalled
Ancestors initBaselineAdmission initInitialCode
Libs preamble wordsLib cv_transLib
open wordsTheory initParamsTheory initBootstrapTheory initSubmissionTheory
  initMachineTheory miscTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
Theorem program_domain_below_dispatch:
  initialPc <= a /\ a < initialPc + codeSizeLimit /\
  a + ffiOffset * (candidateSubmission.first+2) < candidateSubmission.anchorPc /\
  candidateSubmission.anchorPc < initialPc + codeSizeLimit ==>
  programDomain candidateSubmission (n2w a)
Proof
  strip_tac >>
  `a < 2**64 /\ candidateSubmission.anchorPc < 2**64` by
    (fs [initialPc_def,codeSizeLimit_def] >> decide_tac) >>
  `~submissionSharedDomain (n2w a)` by metis_tac [code_region_not_shared] >>
  rewrite_tac [programDomain_def,submissionMemoryDomain_def,WORD_EQ_SUB_LADD,
    word_add_n2w,n2w_11] >>
  fs [w2n_n2w,dimword_64,initialPc_def,codeSizeLimit_def,ffiOffset_def] >>
  rpt strip_tac >> decide_tac
QED
Theorem bootstrap_rom_elements:
  !i. i < LENGTH bootstrapBytes ==> EL i baselineRom = EL i bootstrapBytes
Proof
  simp [initBaselineRomTheory.baselineRom_def,EL_APPEND1]
QED
Theorem bootstrap_initially_installed:
  bytes_in_memory (n2w initialPc) bootstrapBytes
    (initialMemory baselineSubmission input) (programDomain baselineSubmission)
Proof
  irule bytes_in_memory_from_elements >> gen_tac >> strip_tac >>
  simp [word_add_n2w,IN_DEF] >>
  `i < 208` by fs [bootstrap_size] >>
  `~submissionSharedDomain (n2w (initialPc+i))` by
    (irule code_region_not_shared >> fs [codeSizeLimit_def]) >>
  conj_tac
  >- (simp [initialMemory_def,initBaselineAdmissionTheory.baselineSubmission_def,
        initBaselineRomTheory.baseline_rom_length,w2n_n2w,dimword_64,
        initialPc_def,bootstrap_rom_elements,bootstrap_size] >> fs [initialPc_def,ADD_COMM]) >>
  irule program_domain_below_dispatch >>
  simp [initBaselineAdmissionTheory.baselineSubmission_def,
    initCompiledMetadataTheory.compiled_first,initialPc_def,codeSizeLimit_def,
    ffiOffset_def,baselineNativePc_def]
QED
Theorem bytes_in_memory_slice:
  bytes_in_memory a bs m md /\ off <= LENGTH bs ==>
  bytes_in_memory (a+n2w off) (TAKE nbytes (DROP off bs)) m md
Proof
  strip_tac >>
  `LENGTH (TAKE off bs) = off` by metis_tac [listTheory.LENGTH_TAKE] >>
  `bytes_in_memory a (TAKE off bs ++ DROP off bs) m md` by fs [TAKE_DROP] >>
  `bytes_in_memory (a+n2w off) (DROP off bs) m md` by
    (fs [bytes_in_memory_APPEND] >> gvs []) >>
  `bytes_in_memory (a+n2w off)
    (TAKE nbytes (DROP off bs) ++ DROP nbytes (DROP off bs)) m md` by fs [TAKE_DROP] >>
  fs [bytes_in_memory_APPEND]
QED
Definition bootstrapSlices_def:
  bootstrapSlices = EVERY (\(pc,instruction).
    initialPc <= pc /\ pc + LENGTH (riscv_enc instruction) <= initialPc + LENGTH bootstrapBytes /\
    TAKE (LENGTH (riscv_enc instruction)) (DROP (pc-initialPc) bootstrapBytes) = riscv_enc instruction)
    bootstrapBlocks
End
val _ = cv_auto_trans bootstrapSlices_def;
val bootstrap_slices = save_thm ("bootstrap_slices",
  check_thm (EQT_ELIM (cv_eval ``bootstrapSlices``)));
Theorem bootstrap_instruction_fetch:
  MEM (pc,instruction) bootstrapBlocks ==>
  bytes_in_memory (n2w pc) (riscv_enc instruction)
    (initialMemory baselineSubmission input) (programDomain baselineSubmission)
Proof
  strip_tac >>
  mp_tac bootstrap_slices >> rewrite_tac [bootstrapSlices_def,EVERY_MEM] >>
  disch_then (qspec_then `(pc,instruction)` mp_tac) >> simp [] >> strip_tac >>
  `pc-initialPc <= LENGTH bootstrapBytes` by decide_tac >>
  `bytes_in_memory (n2w initialPc + n2w (pc-initialPc))
    (TAKE (LENGTH (riscv_enc instruction)) (DROP (pc-initialPc) bootstrapBytes))
    (initialMemory baselineSubmission input) (programDomain baselineSubmission)` by
    (irule bytes_in_memory_slice >> fs [bootstrap_initially_installed]) >>
  `initialPc + (pc-initialPc) = pc` by decide_tac >>
  gvs [word_add_n2w]
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "bootstrap installation assumptions")
  [program_domain_below_dispatch,bootstrap_rom_elements,bootstrap_initially_installed,
   bytes_in_memory_slice,bootstrap_slices,bootstrap_instruction_fetch];
