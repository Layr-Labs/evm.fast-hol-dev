(* Finite target execution follows from encoder correctness and assembler RTC. *)
Theory initEncoderExecution
Ancestors asmProps
Libs preamble
open relationTheory asmPropsTheory;
Theorem asserts_reaches:
  !n ms. asserts n (\k ms. next ms) ms P Q ==>
    ?final. RTC (\s s'. s' = next s) ms final /\ Q final
Proof
  Induct >> rw [asserts_def]
  >- (qexists_tac `next ms` >> simp [] >> irule RTC_SINGLE >> simp []) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `final` >> simp [] >>
  irule RTC_TRANS >> qexists_tac `next ms` >> simp [] >>
  irule RTC_SINGLE >> simp []
QED
Theorem encoder_step_reaches:
  encoder_correct t /\ asm_step t.config s1 instruction s2 /\
  target_state_rel t s1 ms ==>
  ?final. RTC (\s s'. s' = t.next s) ms final /\ target_state_rel t s2 final
Proof
  rw [encoder_correct_def] >>
  first_x_assum (qspecl_then [`s1`,`instruction`,`s2`,`ms`] mp_tac) >>
  simp [] >> strip_tac >>
  first_x_assum (qspec_then `\n ms. ms` mp_tac) >>
  simp [interference_ok_def] >> strip_tac >>
  drule asserts_reaches >> simp []
QED
Theorem encoder_rtc_reaches:
  encoder_correct t ==>
  !s1 s2. RTC (\a b. ?instruction. asm_step t.config a instruction b) s1 s2 ==>
  !ms. target_state_rel t s1 ms ==>
  ?final. RTC (\s s'. s' = t.next s) ms final /\ target_state_rel t s2 final
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac
  >- (qexists_tac `ms` >> simp []) >>
  drule_all encoder_step_reaches >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac [RTC_TRANS]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "encoder execution assumptions")
  [asserts_reaches,encoder_step_reaches,encoder_rtc_reaches];
