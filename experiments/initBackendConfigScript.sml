(* Configuration premises for the exact Pancake compilation input.
   The base configuration proof is adapted from pinned CakeML riscv_configProof;
   see ../CAKEML-LICENSE. *)
Theory initBackendConfig
Ancestors initCompilationInput backendProof initMachineConfig
Libs preamble blastLib
open backendTheory backendProofTheory riscv_configTheory riscv_targetTheory
  initCompilationInputTheory initMachineTheory miscTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val names_tac =
  simp[tlookup_bij_iff] \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

Theorem base_backend_config_ok:
    backend_config_ok riscv_config riscv_backend_config
Proof
  simp[backend_config_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[riscv_backend_config_def]
  >- (EVAL_TAC >> intLib.ARITH_TAC)
  >- names_tac
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  >- (
    fs [stack_removeTheory.store_offset_def,
        stack_removeTheory.store_pos_def]
    \\ every_case_tac \\ fs [] THEN1 EVAL_TAC
    \\ fs [stack_removeTheory.store_list_def]
    \\ fs [INDEX_FIND_CONS_EQ_SOME,EVAL ``INDEX_FIND n f []``]
    \\ rveq \\ fs [] \\ EVAL_TAC)
  \\ fs[stack_removeTheory.max_stack_alloc_def]
  \\ EVAL_TAC \\ intLib.ARITH_TAC
QED


Theorem guest_backend_config_ok:
  backend_config_ok riscv_config (set_oracle guestConfig allocation)
Proof
  mp_tac base_backend_config_ok >>
  simp [backend_config_ok_def,set_oracle_def,guestConfig_def,pancakeRiscvConfig_def,
        data_to_wordTheory.conf_ok_def,data_to_wordTheory.shift_length_def,
        data_to_wordTheory.max_heap_limit_def]
QED
Theorem guest_machine_initial_config_ok:
  mc_init_ok riscv_config (set_oracle guestConfig allocation)
    (challengeMachineConfig pc program shared names nexternal extra)
Proof
  rw [mc_init_ok_def,set_oracle_def,guestConfig_def,pancakeRiscvConfig_def,
      challengeMachineConfig_def,restrictedTarget_def,riscv_target_def] >> EVAL_TAC
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "compiler configuration assumptions")
  [base_backend_config_ok,guest_backend_config_ok,guest_machine_initial_config_ok];
