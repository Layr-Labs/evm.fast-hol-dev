(* Exercise the checked RISC-V encoder through cv_compute. *)
Theory riscvBackendChecks
Ancestors backendRiscvCv
Libs preamble cv_transLib wordsLib
val _ = cv_memLib.use_long_names := true;
val result = cv_eval
  ``riscv_target$riscv_enc
      (asm$Inst (asm$Arith (asm$Binop asm$Add 10 11 (asm$Reg 12)))) =
    [51w;133w;197w;0w]``;
val _ = if null (hyp result) then
  save_thm ("add_instruction_bytes", check_thm (EQT_ELIM result))
  else failwith "encoder regression has assumptions";
