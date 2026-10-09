(* Use the exact compiler computation at the entry point of Pancake's
   semantic correctness theorem; stack/resource premises remain separate. *)
Theory initCorrectnessInput
Ancestors initArtifacts pancakeCorrectnessBridge
Libs preamble
open initCompilationInputTheory initPreparedTheory pan_to_targetProofTheory
  backendTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem guest_no_perf_calls:
  (set_oracle guestConfig allocation).stack_conf.perf_calls = F
Proof
  simp [set_oracle_def,guestConfig_def,pancakeRiscvConfig_def] >> EVAL_TAC
QED
Theorem guest_correctness_layout:
  mc.target.config = riscv_config ==>
  compilerLayout (FST (compile_prog_max
    (set_oracle guestConfig allocation) mc prepared_guest)) =
  SOME (compiledBytes,compiledBitmaps,compiledConfig.lab_conf)
Proof
  strip_tac >>
  (fn goal =>
    let val th = PART_MATCH (lhs o rand) correctness_compiler_layout (lhs (snd goal))
    in mp_tac (Q.INST [`names` |-> `guestNames`] th) goal end) >>
  simp [guest_no_perf_calls,riscv_isa,guest_to_word,
    GSYM top_compile_to_backend,exact_guest_riscv_compilation,compilerLayout_def]
QED
Theorem guest_correctness_compilation:
  mc.target.config = riscv_config ==>
  ?c stack_max.
    compile_prog_max (set_oracle guestConfig allocation) mc prepared_guest =
      (SOME (compiledBytes,compiledBitmaps,c),stack_max) /\
    c.lab_conf = compiledConfig.lab_conf
Proof
  strip_tac >> imp_res_tac guest_correctness_layout >>
  qabbrev_tac `res = compile_prog_max (set_oracle guestConfig allocation) mc prepared_guest` >>
  PairCases_on `res` >> Cases_on `res0` >>
  fs [compilerLayout_def] >> PairCases_on `x` >> fs []
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "correctness input assumptions")
  [guest_no_perf_calls,guest_correctness_layout,guest_correctness_compilation];
