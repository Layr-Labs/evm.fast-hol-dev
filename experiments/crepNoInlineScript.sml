(* A checked specialization for programs with no inline declarations. *)
Theory crepNoInline
Ancestors pan_to_crep
Libs preamble
Theorem inline_empty:
  !p : 'a crepLang$prog. crep_inline$inline_prog FEMPTY p = p
Proof
  gen_tac >> completeInduct_on `crepLang$prog_size (K 0) p` >>
  rw [] >> Cases_on `p` >>
  simp [Once crep_inlineTheory.inline_prog_def] >>
  rpt CASE_TAC >> gvs [crepLangTheory.prog_size_def]
QED
Theorem no_inline_top:
  !ps : (mlstring # num list # 'a crepLang$prog) list.
    crep_inline$compile_inl_top [] ps = ps
Proof
  simp [crep_inlineTheory.compile_inl_top_def, crep_inlineTheory.compile_inl_prog_def,
    inline_empty, pairTheory.pair_CASE_def, ELIM_UNCURRY]
QED
Theorem no_inline_compile:
  MAP FST (panLang$functions (FILTER panLang$inlinable ps)) = [] ==>
  pan_to_crep$compile_prog ps = pan_to_crep$compile_to_crep ps
Proof
  simp [pan_to_crepTheory.compile_prog_def, no_inline_top]
QED
