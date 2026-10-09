(* Checked optimized word program used by the stack-bound certificate. *)
Theory initStackInput
Ancestors initBytecode
Libs preamble cv_transLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null(hyp th) then save_thm(name,check_thm th)
  else failwith (name ^ " has assumptions");
val result = cv_eval_pat (cvName "optimized_word_result")
  ``riscvBackendDefs$word_to_word_inlogic_riscv
    (set_oracle guestConfig allocation).word_to_word_conf prepared_word``;
val checked_optimized_word_result = save_closed "checked_optimized_word_result" result;
val optimized_word_succeeded = save_closed "optimized_word_succeeded"
  (EQT_ELIM (cv_eval ``IS_SOME optimized_word_result``));
Definition optimized_word_def:
  optimized_word = case optimized_word_result of
    NONE => [] | SOME (col,prog) => prog
End
Definition optimized_colours_def:
  optimized_colours = case optimized_word_result of
    NONE => [] | SOME (col,prog) => col
End
val _ = cv_auto_trans optimized_word_def;
val _ = cv_auto_trans optimized_colours_def;
Theorem optimized_word_compilation:
  word_to_word$compile (set_oracle guestConfig allocation).word_to_word_conf
    riscv_config prepared_word = (optimized_colours,optimized_word)
Proof
  `?out. optimized_word_result = SOME out` by
    metis_tac [optimized_word_succeeded,optionTheory.IS_SOME_EXISTS] >>
  PairCases_on `out` >>
  mp_tac (checked_optimized_word_result |>
    REWRITE_RULE [GSYM riscvBackendDefsTheory.word_to_word_inlogic_riscv_eq]) >>
  asm_rewrite_tac [] >>
  disch_then (assume_tac o MATCH_MP
    pancakeBackendBridgeTheory.word_to_word_inlogic_thm) >>
  simp [optimized_word_def,optimized_colours_def]
QED
val _ = if null(hyp optimized_word_compilation)
  then ignore(check_thm optimized_word_compilation)
  else failwith "optimized word compilation assumptions";
val _ = save_closed "optimized_word_function_count"
  (cv_eval ``LENGTH optimized_word``);
