(* Concrete frame sizes for the checked optimized word program. *)
Theory initStackFrames
Ancestors initStackInput backendProof
Libs preamble cv_transLib
open word_to_stackTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
Definition frameWords_def:
  frameWords available argc (prog:64 wordLang$prog) =
    let slots = MAX ((wordLang$max_var prog DIV 2 + 1) - available)
                    (argc - available)
    in if slots = 0 then 0 else slots + 1
End
val _ = cv_auto_trans frameWords_def;
Theorem compile_prog_frame:
  FST (SND (word_to_stack$compile_prog ac perf (prog:64 wordLang$prog) argc available bm)) =
  frameWords available argc prog
Proof
  rw [word_to_stackTheory.compile_prog_def,frameWords_def] >>
  pairarg_tac >> simp []
QED
Definition optimized_frames_def:
  optimized_frames = fromAList
    (MAP (\(n,a,p).
      (n,frameWords (riscv_config.reg_count -
                    (5 + LENGTH riscv_config.avoid_regs)) a p)) optimized_word)
End
val _ = cv_auto_trans (optimized_frames_def |>
  SIMP_RULE (srw_ss()) [riscv_targetTheory.riscv_config_def]);
Definition optimized_frame_max_def:
  optimized_frame_max = MAX_LIST (MAP SND (toAList optimized_frames))
End
val _ = cv_auto_trans optimized_frame_max_def;
val maximum = cv_eval ``optimized_frame_max``;
val _ = print (thm_to_string maximum ^ "\n");
val _ = if null(hyp maximum) then save_thm("optimized_frame_maximum",check_thm maximum)
  else failwith "frame maximum assumptions";
