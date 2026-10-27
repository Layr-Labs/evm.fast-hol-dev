(* No instruction in the fixed bootstrap overlaps an FFI dispatch entry. *)
Theory initBootstrapFfi
Ancestors initBootstrapInstalled targetProps
Libs preamble cv_transLib wordsLib
open wordsTheory initParamsTheory initBootstrapTheory initMachineTheory
  initSubmissionTheory initBaselineAdmissionTheory initCompiledMetadataTheory
  initBootstrapInstalledTheory targetPropsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
Definition baselineFfiPcs_def:
  baselineFfiPcs =
    GENLIST (\i. n2w baselineNativePc - n2w ((3+i)*ffiOffset):word64) compiledFirst ++
    MAP (\rec:init_mmio. n2w baselineNativePc + n2w rec.entry_pc) baselineExtra
End
val _ = cv_auto_trans baselineFfiPcs_def;
Theorem baseline_ffi_pcs:
  (submissionConfig baselineSubmission).ffi_entry_pcs = baselineFfiPcs
Proof
  simp [submissionConfig_def,baselineSubmission_def,challengeMachineConfig_def,
        baselineFfiPcs_def]
QED
Definition bootstrapFfiAbove_def:
  bootstrapFfiAbove = EVERY (\pc. initialPc + 208 <= w2n pc) baselineFfiPcs
End
val _ = cv_auto_trans bootstrapFfiAbove_def;
val bootstrap_ffi_above = save_thm ("bootstrap_ffi_above",check_thm
  (EQT_ELIM (cv_eval ``bootstrapFfiAbove``)
   |> REWRITE_RULE [bootstrapFfiAbove_def]));
Theorem bootstrap_range_ffi_disjoint:
  initialPc <= pc /\ pc+nbytes <= initialPc+208 /\ s.pc = n2w pc ==>
  ffi_entry_pcs_disjoint (submissionConfig baselineSubmission) s nbytes
Proof
  strip_tac >>
  mp_tac bootstrap_ffi_above >> simp [EVERY_MEM] >> strip_tac >>
  simp [ffi_entry_pcs_disjoint_def,baseline_ffi_pcs,DISJOINT_ALT] >>
  rpt strip_tac >> fs [GSPECIFICATION] >>
  qpat_x_assum `!pc. MEM pc baselineFfiPcs ==> _`
    (qspec_then `n2w a + n2w pc` mp_tac) >>
  simp [word_add_n2w,w2n_n2w,dimword_64] >>
  fs [initialPc_def] >> decide_tac
QED
Theorem bootstrap_instruction_ffi_disjoint:
  MEM (pc,instruction) bootstrapBlocks /\ s.pc = n2w pc ==>
  ffi_entry_pcs_disjoint (submissionConfig baselineSubmission) s
    (LENGTH (riscv_enc instruction))
Proof
  strip_tac >> irule bootstrap_range_ffi_disjoint >>
  qexists_tac `pc` >> simp [] >>
  mp_tac bootstrap_slices >> simp [bootstrapSlices_def,EVERY_MEM] >>
  disch_then (qspec_then `(pc,instruction)` mp_tac) >> simp [bootstrap_size]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "bootstrap FFI separation assumptions")
  [baseline_ffi_pcs,bootstrap_ffi_above,bootstrap_range_ffi_disjoint,
   bootstrap_instruction_ffi_disjoint];
