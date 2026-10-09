(* Compiler machine-configuration premise for the fixed restricted target. *)
Theory initMachineConfig
Ancestors initRestrictedEncoder lab_to_targetProof
Libs preamble wordsLib
open initMachineTheory initRestrictedTargetTheory initRestrictedEncoderTheory
  asmPropsTheory riscv_targetTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val target_config = SIMP_CONV (srw_ss()) [restricted_target_expanded]
  ``restrictedTarget.config``;
Theorem restricted_encoding_ok:
  enc_ok riscv_config
Proof
  mp_tac restricted_encoder_correct >>
  simp [encoder_correct_def,target_ok_def,target_config]
QED
Theorem challenge_machine_config_ok:
  mc_conf_ok (challengeMachineConfig pc program shared names nexternal extra)
Proof
  simp [lab_to_targetProofTheory.mc_conf_ok_def,challengeMachineConfig_def,
        restricted_encoder_correct,target_config,restricted_encoding_ok] >>
  simp [miscTheory.good_dimindex_def,asmTheory.reg_ok_def,riscv_config_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "machine configuration assumptions")
  [restricted_encoding_ok,challenge_machine_config_ok];
