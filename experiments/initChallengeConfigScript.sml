(* The fixed cache-hook evaluator never consults the installation callback. *)
Theory initChallengeConfig
Ancestors initMachine
Libs preamble
open targetSemTheory initMachineTheory miscTheory;
Theorem install_next_update_commute[local]:
  ((mc with install_interfer := callback) with next_interfer := next) =
  ((mc with next_interfer := next) with install_interfer := callback)
Proof
  simp [machine_config_component_equality]
QED
Theorem install_ffi_update_commute[local]:
  ((mc with install_interfer := callback) with ffi_interfer := ffi_callback) =
  ((mc with ffi_interfer := ffi_callback) with install_interfer := callback)
Proof
  simp [machine_config_component_equality]
QED
Theorem read_arrays_install[local]:
  read_ffi_bytearrays (mc with install_interfer := callback) ms =
  read_ffi_bytearrays mc ms
Proof
  simp [read_ffi_bytearrays_def,read_ffi_bytearray_def]
QED
Theorem challenge_install_callback_irrelevant:
  !k (mc:(64,riscv_state,'c)machine_config) ffi ms callback.
    challengeEvaluate (mc with install_interfer := callback) ffi k ms =
    challengeEvaluate mc ffi k ms
Proof
  Induct >> rpt gen_tac >>
  CONV_TAC (BINOP_CONV (REWR_CONV challengeEvaluate_def)) >>
  simp [read_arrays_install] >>
  rpt (TOP_CASE_TAC >> fs [apply_oracle_def,read_arrays_install]) >> fs [] >>
  once_rewrite_tac [install_next_update_commute,install_ffi_update_commute] >> simp []
QED
val _ = if null(hyp challenge_install_callback_irrelevant)
  then ignore(check_thm challenge_install_callback_irrelevant)
  else failwith "challenge callback independence assumptions";
