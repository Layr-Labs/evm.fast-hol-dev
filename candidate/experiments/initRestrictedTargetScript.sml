(* Explicit projections for the challenge target, for encoder proof reuse. *)
Theory initRestrictedTarget
Ancestors initRestrictedRules
Libs preamble
open initMachineTheory riscv_targetTheory;
Definition restrictedNext_def:
  restrictedNext s = THE (restrictedNextRISCV s)
End
Theorem restricted_target_expanded:
  restrictedTarget =
    <| next := restrictedNext; config := riscv_config;
       get_pc := (\s. s.c_PC s.procID);
       get_reg := (\s. s.c_gpr s.procID o n2w);
       get_byte := riscv_state_MEM8; state_ok := riscv_ok; proj := riscv_proj |>
Proof
  simp [restrictedTarget_def,riscv_target_def,GSYM restrictedNext_def,ETA_AX]
QED
val _ = if null(hyp restricted_target_expanded)
  then ignore(check_thm restricted_target_expanded)
  else failwith "restricted target projection assumptions";
