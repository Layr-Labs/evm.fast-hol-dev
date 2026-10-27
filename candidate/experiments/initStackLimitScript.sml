(* Apply the checked stack certificate to the full Pancake compilation. *)
Theory initStackLimit
Ancestors initStackCertificate initStackFrameProof initCorrectnessInput
Libs preamble
open initStackCertificateTheory initStackFrameProofTheory initStackInputTheory
  initCompilationInputTheory initCorrectnessInputTheory
  pan_to_targetProofTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem guest_stack_maximum:
  mc.target.config = riscv_config ==>
  SND (compile_prog_max (set_oracle guestConfig allocation) mc prepared_guest) =
  word_depth$max_depth optimized_frames (word_depth$full_call_graph 64 optimized_code)
Proof
  rw [compile_prog_max_def,guest_to_word,riscv_isa,optimized_word_compilation] >>
  pairarg_tac >> gvs [] >> drule optimized_frame_map >>
  simp [optimized_code_def,InitGlobals_location_eq_first_name,
        crep_to_loopTheory.first_name_def]
QED
Theorem guest_stack_bound:
  mc.target.config = riscv_config ==>
  ?depth. SND (compile_prog_max (set_oracle guestConfig allocation) mc prepared_guest) =
    SOME depth /\ depth <= 7480
Proof
  metis_tac [guest_stack_maximum,optimized_stack_bound]
QED
Theorem guest_bounded_compilation:
  mc.target.config = riscv_config ==>
  ?c depth.
    compile_prog_max (set_oracle guestConfig allocation) mc prepared_guest =
      (SOME (compiledBytes,compiledBitmaps,c),SOME depth) /\
    c.lab_conf = compiledConfig.lab_conf /\ depth <= 7480
Proof
  strip_tac >> imp_res_tac guest_correctness_compilation >>
  imp_res_tac guest_stack_bound >> gvs [] >> metis_tac []
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "compiled stack bound assumptions")
  [guest_stack_maximum,guest_stack_bound,guest_bounded_compilation];
