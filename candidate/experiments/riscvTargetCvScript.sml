Theory riscvTargetCv
Ancestors riscvEncodeCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
Theorem bit11_32:
  !w : word32. w ' 11 = word_bit 11 w
Proof
  simp [wordsTheory.word_bit_def]
QED
Theorem bit31_64:
  !w : word64. w ' 31 = word_bit 31 w
Proof
  simp [wordsTheory.word_bit_def]
QED
val _ = cv_auto_trans (riscv_targetTheory.riscv_const32_def
  |> SRULE [bit11_32, bit31_64]);
fun apply_eqs th =
  CONJUNCTS th |> map (fn t =>
    let val t = SPEC_ALL t
        val ty = fst (dom_rng (type_of (lhs (concl t))))
    in AP_THM t (mk_var ("arg",ty)) end) |> LIST_CONJ;
val _ = cv_auto_trans (apply_eqs riscv_targetTheory.riscv_bop_r_def);
val bop_pre = cv_auto_trans_pre "" (apply_eqs riscv_targetTheory.riscv_bop_i_def);
Theorem bop_i_pre[cv_pre]:
  !b arg. b <> asm$Sub ==> riscv_target_riscv_bop_i_pre b arg
Proof
  Cases >> simp [bop_pre]
QED
val sh_pre = cv_auto_trans_pre "" (apply_eqs riscv_targetTheory.riscv_sh_def);
Theorem shift_i_pre[cv_pre]:
  !s arg. s <> Ror ==> riscv_target_riscv_sh_pre s arg
Proof
  Cases >> simp [sh_pre]
QED
val shv_pre = cv_auto_trans_pre "" (apply_eqs riscv_targetTheory.riscv_shv_def);
Theorem shift_r_pre[cv_pre]:
  !s arg. s <> Ror ==> riscv_target_riscv_shv_pre s arg
Proof
  Cases >> simp [shv_pre]
QED
(* Split the memory-operation equation before eliminating its sum of functions. *)
val ast_eqs = riscv_targetTheory.riscv_ast_def |> CONJUNCTS |>
  map (fn th =>
    let val th = SPEC_ALL th
        val vars = free_vars (concl th)
    in case List.find (fn v => type_of v = ``:asm$memop``) vars of
      NONE => th
    | SOME v => LIST_CONJ (map (fn c => INST [v |-> c] th)
        [``asm$Load``, ``asm$Load32``, ``asm$Load16``, ``asm$Load8``,
         ``asm$Store``, ``asm$Store32``, ``asm$Store16``, ``asm$Store8``])
    end) |> LIST_CONJ |>
  SRULE [bit11_32, bit31_64, riscv_targetTheory.riscv_memop_def];
val ast_pre = cv_auto_trans_pre "" ast_eqs;
Theorem riscv_ast_pre[cv_pre]:
  !v. riscv_target_riscv_ast_pre v
Proof
  Cases >> simp [Once ast_pre, bop_pre, sh_pre, shv_pre] >>
  rpt (CHANGED_TAC (simp [Once ast_pre, bop_pre, sh_pre, shv_pre]) ORELSE
       (first_x_assum kall_tac))
QED
val _ = cv_auto_trans (riscv_targetTheory.riscv_enc_def |>
  SRULE [combinTheory.o_DEF, LIST_BIND_def, FUN_EQ_THM]);
