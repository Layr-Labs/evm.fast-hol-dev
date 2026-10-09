Theory initCompilationInput
Ancestors initWord backendRiscvCv riscv_config numSortCv
Libs preamble cv_transLib recordLiteralLib
val _ = cv_memLib.use_long_names := true;
Theorem guest_to_word:
  pan_to_word$compile_prog RISC_V prepared_guest = prepared_word
Proof
  simp [pan_to_wordTheory.compile_prog_def,
        initPreparedTheory.prepared_simplified, initPreparedTheory.prepared_structures, initPreparedTheory.prepared_global_declarations,
        initPreparedTheory.prepared_crep_compilation, initLoopsTheory.prepared_loop_compilation, prepared_word_compilation]
QED
Definition pancakeRiscvConfig_def:
  pancakeRiscvConfig = riscv_backend_config with
    data_conf updated_by (\c. c with gc_kind := None)
End
val _ = cv_trans_deep_embedding recordLiteralLib.normalize pancakeRiscvConfig_def;
Definition guestNames_def:
  guestNames = sptree$union
    (sptree$fromAList (word_to_stack$stub_names () ++
                       stack_alloc$stub_names () ++ stack_remove$stub_names ()))
    (sptree$fromAList (ZIP (sort $< (MAP FST prepared_word),
                          «generated_main» :: MAP FST (functions prepared_guest))))
End
val _ = cv_auto_trans guestNames_def;
Definition guestConfig_def:
  guestConfig = pancakeRiscvConfig with exported := pan_to_target$exports guestAst
End
val _ = cv_auto_trans guestConfig_def;

Theorem riscv_isa:
  riscv_target$riscv_config.ISA = RISC_V
Proof
  EVAL_TAC
QED
Theorem top_compile_to_backend:
  pan_to_target$compile_prog riscv_target$riscv_config
    (set_oracle pancakeRiscvConfig oracle) guestAst =
  backend$from_word_0 riscv_target$riscv_config
    (set_oracle guestConfig oracle) guestNames prepared_word
Proof
  rewrite_tac [pan_to_targetTheory.compile_prog_eq, initSimplifyTheory.literal_fun_decl,
    GSYM initPreparedTheory.mainFirst_def] >>
  simp [initPreparedTheory.guest_main_first, riscv_isa, guest_to_word,
        guestNames_def, guestConfig_def, backendTheory.set_oracle_def]
QED
