(* Restricted counterparts of the step evaluator's symbolic execution rules. *)
Theory initRestrictedRules
Ancestors initRestrictedStep
Libs preamble
open riscvTheory riscv_stepTheory initMachineTheory initTargetTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem restricted_decoded_word:
  DecodeAny (Word w) = instruction /\ supported_instruction instruction ==>
  restrictedDecodeAny (Word w) = instruction
Proof
  simp [DecodeAny_def,restrictedDecodeAny_def,restricted_decode_def] >>
  metis_tac []
QED
Theorem restricted_next_normal:
  Fetch s = (w,s') /\ restrictedDecodeAny w = instruction /\
  Run instruction s' = nxt /\ nxt.exception = NoException /\
  nxt.c_NextFetch nxt.procID = NONE ==>
  restrictedNextRISCV s = update_pc (nxt.c_PC nxt.procID + Skip nxt) nxt
Proof
  simp [restrictedNextRISCV_def,PC_def,NextFetch_def]
QED
Theorem restricted_next_branch:
  Fetch s = (w,s') /\ restrictedDecodeAny w = instruction /\
  Run instruction s' = nxt /\ nxt.exception = NoException /\
  nxt.c_NextFetch nxt.procID = SOME (BranchTo a) ==>
  restrictedNextRISCV s =
    update_pc a (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch)
Proof
  simp [restrictedNextRISCV_def,PC_def,NextFetch_def,write'NextFetch_def]
QED
Theorem restricted_next_cond_branch:
  Fetch s = (w,s') /\ restrictedDecodeAny w = instruction /\
  Run instruction s' = nxt /\ nxt.exception = NoException /\
  nxt.c_NextFetch nxt.procID = (if b then SOME (BranchTo a) else NONE) ==>
  restrictedNextRISCV s =
    update_pc (if b then a else nxt.c_PC nxt.procID + Skip nxt)
      (nxt with c_NextFetch := (nxt.procID =+ NONE) nxt.c_NextFetch)
Proof
  Cases_on `b` >>
  simp [restrictedNextRISCV_def,PC_def,NextFetch_def,write'NextFetch_def] >>
  strip_tac >> AP_TERM_TAC >>
  simp [riscv_state_component_equality,combinTheory.UPDATE_APPLY_IMP_ID]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "restricted symbolic rule assumptions")
  [restricted_decoded_word,restricted_next_normal,
   restricted_next_branch,restricted_next_cond_branch];
