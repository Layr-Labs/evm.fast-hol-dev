(* Local execution agreement for dynamically fetched supported instructions. *)
Theory initRestrictedStep
Ancestors initMachine
Libs preamble
open initMachineTheory initTargetTheory riscv_stepTheory riscv_targetTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem restricted_decode_any_word:
  supported_instruction (riscv$Decode w) ==>
  restrictedDecodeAny (riscv$Word w) = DecodeAny (riscv$Word w)
Proof
  simp [restrictedDecodeAny_def,DecodeAny_def,supported_decode]
QED
Theorem restricted_step_agrees:
  Fetch s = (riscv$Word w,fetched) /\
  supported_instruction (riscv$Decode w) ==>
  restrictedNextRISCV s = NextRISCV s
Proof
  simp [restrictedNextRISCV_def,NextRISCV_def,restricted_decode_any_word]
QED
Theorem restricted_target_next_agrees:
  Fetch s = (riscv$Word w,fetched) /\
  supported_instruction (riscv$Decode w) ==>
  restrictedTarget.next s = riscv_target.next s
Proof
  simp [restrictedTarget_def,riscv_target_def,riscv_next_def] >>
  metis_tac [restricted_step_agrees]
QED
Theorem restricted_target_state_relation:
  asmProps$target_state_rel restrictedTarget a s =
  asmProps$target_state_rel riscv_target a s
Proof
  simp [asmPropsTheory.target_state_rel_def,restrictedTarget_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "restricted step agreement assumptions")
  [restricted_decode_any_word,restricted_step_agrees,
   restricted_target_next_agrees,restricted_target_state_relation];
