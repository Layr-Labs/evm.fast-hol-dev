(* Frame properties of the fixed challenge's FFI return operations. *)
Theory initMachineReturn
Ancestors initRestrictedStep
Libs preamble wordsLib
open asmSemTheory asmPropsTheory riscv_targetTheory initMachineTheory
  miscTheory wordsTheory;
Theorem machine_set_pc_ok:
  riscv_ok s /\ aligned 2 pc ==> riscv_ok (machineSetPc s pc)
Proof
  simp [riscv_ok_def,machineSetPc_def,APPLY_UPDATE_THM]
QED
Theorem machine_set_reg_ok:
  riscv_ok (machineSetReg s r w) = riscv_ok s
Proof
  simp [riscv_ok_def,machineSetReg_def]
QED
Theorem machine_ext_return_relation:
  target_state_rel restrictedTarget t ms /\ aligned 2 (t.regs 1) ==>
  target_state_rel restrictedTarget
    (t with <|pc := t.regs 1;
              mem := asm_write_bytearray (t.regs 12) bytes t.mem|>)
    (machineExtReturn ms bytes)
Proof
  strip_tac >>
  `ms.c_gpr ms.procID 1w = t.regs 1 /\
   ms.c_gpr ms.procID 12w = t.regs 12` by
    (fs [target_state_rel_def,restrictedTarget_def,riscv_target_def,riscv_config_def] >>
     metis_tac []) >>
  fs [target_state_rel_def,restrictedTarget_def,riscv_target_def,
      machineExtReturn_def,machineSetPc_def,riscv_ok_def,riscv_config_def,APPLY_UPDATE_THM] >>
  rpt strip_tac >> irule mem_eq_imp_asm_write_bytearray_eq >> metis_tac []
QED
Theorem machine_set_reg_pc_relation:
  target_state_rel restrictedTarget t ms /\ r < 32 /\ aligned 2 pc ==>
  target_state_rel restrictedTarget
    (t with <|regs := (r =+ value) t.regs; pc := pc|>)
    (machineSetPc (machineSetReg ms r value) pc)
Proof
  rw [target_state_rel_def,restrictedTarget_def,riscv_target_def,riscv_config_def,
      machineSetPc_def,machineSetReg_def,riscv_ok_def,APPLY_UPDATE_THM] >>
  fs [n2w_11,dimword_def]
QED
Theorem machine_mmio_read_relation:
  target_state_rel restrictedTarget t ms /\ r < 32 /\ aligned 2 pc ==>
  target_state_rel restrictedTarget
    (t with <|regs := (r =+ word_of_bytes F 0w bytes) t.regs; pc := pc|>)
    (machineMmioReturn ms (SharedMem MappedRead) (nb,a,r,pc) bytes)
Proof
  simp [machineMmioReturn_def,machine_set_reg_pc_relation]
QED
Theorem machine_mmio_write_relation:
  target_state_rel restrictedTarget t ms /\ aligned 2 pc ==>
  target_state_rel restrictedTarget (t with pc := pc)
    (machineMmioReturn ms (SharedMem MappedWrite) (nb,a,r,pc) bytes)
Proof
  simp [machineMmioReturn_def,machineSetPc_def,target_state_rel_def,
        restrictedTarget_def,riscv_target_def,riscv_ok_def,riscv_config_def,APPLY_UPDATE_THM]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "machine return assumptions")
  [machine_set_pc_ok,machine_set_reg_ok,machine_ext_return_relation,
   machine_set_reg_pc_relation,machine_mmio_read_relation,
   machine_mmio_write_relation];
