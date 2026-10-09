(* RISC-V instance of CakeML's backend_arm8_cv translation structure.
   Source: pinned CakeML submodule, cv_translator/backend_arm8_cvScript.sml. *)
Theory riscvEncodeCv
Ancestors backend_64_cv backend_riscv riscv_target
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;

val _ = List.app (fn th => ignore (cv_auto_trans th))
  [riscvTheory.Rtype_def, riscvTheory.R4type_def,
   riscvTheory.Itype_def, riscvTheory.Stype_def, riscvTheory.SBtype_def,
   riscvTheory.Utype_def, riscvTheory.UJtype_def, riscvTheory.opc_def,
   riscvTheory.amofunc_def];
val _ = cv_auto_trans riscvTheory.Encode_def;
