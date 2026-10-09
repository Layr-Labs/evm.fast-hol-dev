(* Connect the compact frame computation to the ordinary stack compiler. *)
Theory initStackFrameProof
Ancestors initStackFrames
Libs preamble
open word_to_stackTheory backendProofTheory initStackFramesTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = print (thm_to_string optimized_frame_maximum ^ "\n");
val result_stream = TextIO.openOut "stack-frame-maximum.txt";
val _ = TextIO.output (result_stream,thm_to_string optimized_frame_maximum ^ "\n");
val _ = TextIO.closeOut result_stream;
Theorem compile_frame_map:
  word_to_stack$compile ac F (prog:(num # num # 64 wordLang$prog) list) =
    (bm,c,fs,p) ==>
  c.stack_frame_size = fromAList
    (MAP (\(n,a,body). (n,frameWords
      (ac.reg_count - (5 + LENGTH ac.avoid_regs)) a body)) prog)
Proof
  rw [word_to_stackTheory.compile_def] >> pairarg_tac >> gvs [] >>
  drule compile_word_to_stack_sfs_aux >> simp [compile_prog_frame] >>
  disch_then (assume_tac o SYM) >> asm_rewrite_tac [] >>
  AP_TERM_TAC >> irule listTheory.MAP_CONG >>
  simp [pairTheory.FORALL_PROD]
QED
Theorem optimized_frame_map:
  word_to_stack$compile riscv_config F optimized_word = (bm,c,fs,p) ==>
  c.stack_frame_size = optimized_frames
Proof
  strip_tac >> drule compile_frame_map >> simp [optimized_frames_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "frame correspondence assumptions")
  [compile_frame_map,optimized_frame_map];
