(* Relate the compiler used for concrete evaluation to the resource-aware
   compiler appearing in Pancake's semantic correctness theorem. *)
Theory pancakeCorrectnessBridge
Ancestors pan_to_targetProof
Libs preamble
open backendTheory;
Definition compilerLayout_def:
  compilerLayout result =
    OPTION_MAP (\(bytes,bitmaps,c). (bytes,bitmaps,c.lab_conf)) result
End
Theorem compilerLayout_attach:
  compilerLayout (attach_bitmaps names c bm result) =
  OPTION_MAP (\(bytes,lc). (bytes,bm,lc)) result
Proof
  Cases_on `result` >> simp [compilerLayout_def,attach_bitmaps_def] >>
  PairCases_on `x` >> simp [compilerLayout_def,attach_bitmaps_def]
QED
Theorem correctness_compiler_layout:
  c.stack_conf.perf_calls = F ==>
  compilerLayout (FST (compile_prog_max c mc prog)) =
  compilerLayout (from_word_0 mc.target.config c names
    (pan_to_word$compile_prog mc.target.config.ISA prog))
Proof
  rw [compile_prog_max_def,from_word_0_def,from_word_def,LET_DEF] >>
  rpt (pairarg_tac >> fs []) >>
  simp [from_stack_def,from_lab_def,compilerLayout_attach,LET_DEF]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "compiler bridge assumptions")
  [compilerLayout_attach,correctness_compiler_layout];
