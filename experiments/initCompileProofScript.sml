Theory initCompileProof
Ancestors initBytecode
Libs preamble
(* Avoid pretty-printing giant evaluated literals into HTML documentation. *)
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;

(* Use the checked success theorem to expose the result shape. Do not expand
   the megabyte-sized cv literal merely to match the correspondence theorem. *)
Theorem guest_riscv_compilation:
  ?bm c. pan_to_target$compile_prog riscv_config
    (set_oracle pancakeRiscvConfig allocation) guestAst =
    SOME (compiledBytes,bm,c)
Proof
  `?out. backend_output = SOME out` by
    metis_tac [backend_succeeded,optionTheory.IS_SOME_EXISTS] >>
  PairCases_on `out` >>
  mp_tac (checked_backend_output |>
    REWRITE_RULE [GSYM riscvBackendDefsTheory.from_word_0_riscv_eq]) >>
  asm_rewrite_tac [] >>
  disch_then (strip_assume_tac o MATCH_MP pancakeBackendBridgeTheory.from_word_0_thm) >>
  simp [initCompilationInputTheory.top_compile_to_backend,compiledBytes_def] >>
  metis_tac []
QED
val _ = if null (hyp guest_riscv_compilation)
  then ignore (check_thm guest_riscv_compilation)
  else failwith "guest compilation has assumptions";
