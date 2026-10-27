(* Auxiliary configuration for applying CakeML's compiler theorem.
   The fixed challenge configuration/evaluator are unchanged. A separate
   no-install simulation is still required to connect native execution. *)
Theory initCompilerMachine
Ancestors initFfiInstallation initChallengeConfig
Libs preamble wordsLib
open asmSemTheory asmPropsTheory targetSemTheory initMachineTheory
  initSubmissionTheory initMachineReturnTheory riscv_targetTheory wordsTheory;
Definition compilerInstallReturn_def:
  compilerInstallReturn ms bytes =
    machineSetPc
      (machineSetReg (machineExtReturn ms bytes) 10 (ms.c_gpr ms.procID 12w))
      (ms.c_gpr ms.procID 1w)
End
Definition compilerMachineConfig_def:
  compilerMachineConfig s = submissionConfig s with
    install_interfer := (\n (bytes,ms). compilerInstallReturn ms bytes)
End
Theorem compiler_install_return_relation:
  target_state_rel restrictedTarget t ms /\ aligned 2 (t.regs 1) ==>
  target_state_rel restrictedTarget
    (t with <|regs := (10 =+ t.regs 12) t.regs;
              mem := asm_write_bytearray (t.regs 12) bytes t.mem;
              pc := t.regs 1|>)
    (compilerInstallReturn ms bytes)
Proof
  strip_tac >>
  `ms.c_gpr ms.procID 1w = t.regs 1 /\
   ms.c_gpr ms.procID 12w = t.regs 12` by
    (fs [target_state_rel_def,restrictedTarget_def,riscv_target_def,riscv_config_def] >>
     metis_tac []) >>
  `target_state_rel restrictedTarget
    (t with <|pc := t.regs 1; mem := asm_write_bytearray (t.regs 12) bytes t.mem|>)
    (machineExtReturn ms bytes)` by
    (irule machine_ext_return_relation >> simp []) >>
  mp_tac (Q.INST
    [`t` |-> `t with <|pc := t.regs 1;
                        mem := asm_write_bytearray (t.regs 12) bytes t.mem|>`,
     `ms` |-> `machineExtReturn ms bytes`, `r` |-> `10`,
     `value` |-> `t.regs 12`, `pc` |-> `t.regs 1`]
    machine_set_reg_pc_relation) >>
  simp [compilerInstallReturn_def]
QED
Theorem compiler_install_interference:
  install_interfer_ok pc cbspace (compilerMachineConfig s)
Proof
  rw [install_interfer_ok_def,compilerMachineConfig_def,submissionConfig_def,
      challengeMachineConfig_def,restrictedTarget_def,riscv_target_def,riscv_config_def] >>
  drule (SIMP_RULE (srw_ss())
    [restrictedTarget_def,riscv_target_def,riscv_config_def]
    compiler_install_return_relation) >>
  disch_then (qspec_then `bytes` mp_tac) >>
  simp [target_state_rel_def,APPLY_UPDATE_THM] >> metis_tac []
QED
Theorem ffi_install_callback_irrelevant:
  ffi_interfer_ok pc (mc with install_interfer := callback) = ffi_interfer_ok pc mc
Proof
  simp [ffi_interfer_ok_def,read_ffi_bytearray_def,read_ffi_bytearrays_def]
QED
Theorem compiler_ffi_interference:
  admitted s ==> ffi_interfer_ok pc (compilerMachineConfig s)
Proof
  simp [compilerMachineConfig_def,ffi_install_callback_irrelevant,
        initFfiInstallationTheory.admitted_ffi_interference]
QED
Theorem compiler_config_challenge_evaluation:
  challengeEvaluate (compilerMachineConfig s) ffi k ms =
  challengeEvaluate (submissionConfig s) ffi k ms
Proof
  simp [compilerMachineConfig_def,challenge_install_callback_irrelevant]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "auxiliary compiler-machine assumptions")
  [compiler_install_return_relation,compiler_install_interference,
   ffi_install_callback_irrelevant,compiler_ffi_interference,
   compiler_config_challenge_evaluation];
