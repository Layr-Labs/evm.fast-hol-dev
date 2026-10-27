(* CakeML-derived portions are covered by ../CAKEML-LICENSE. *)
Theory backendRiscvCv
Ancestors riscvTargetCv riscvBackendDefs backend_64_cv backend_cv to_data_cv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := false;
(* The target-specific backend definitions are polymorphic in the word
   size; fix it to the target's word size before translating. *)
fun word_tyvars ty =
  case total dest_thy_type ty of
    NONE => []
  | SOME {Thy="fcp",Tyop="cart",Args=[_,v]} =>
      if is_vartype v then [v] else word_tyvars v
  | SOME {Thy="wordLang",Tyop=("prog"|"exp"),Args=[v]} =>
      if is_vartype v then [v] else word_tyvars v
  | SOME {Args,...} => List.concat (map word_tyvars Args);

fun arch_spec th =
  find_terms (K true) (concl th)
  |> List.concat o map (word_tyvars o type_of) |> mk_set
  |> map (fn v => v |-> “:64”)
  |> (fn s => INST_TYPE s th);

(*---------------------------------------------------------------------------*
  Remaining riscv-specific functions
 *---------------------------------------------------------------------------*)

val pre = cv_auto_trans_pre "" (comp_riscv_def |> arch_spec);

Theorem comp_riscv_pre[cv_pre,local]:
  ∀perf v bs kf. comp_riscv_pre perf v bs kf
Proof
  gen_tac \\ gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_auto_trans (compile_prog_riscv_def |> arch_spec);

val pre = cv_auto_trans_pre "" (compile_word_to_stack_riscv_def |> arch_spec);

Theorem compile_word_to_stack_riscv_pre[cv_pre]:
  ∀perf k v bitmaps. compile_word_to_stack_riscv_pre perf k v bitmaps
Proof
  Induct_on`v`
  \\ rw [] \\ simp [Once pre]
QED

Theorem fp_reg_ok_riscv_def[local,cv_inline] = (fp_reg_ok_riscv_def |> arch_spec);

val _ = cv_auto_trans (inst_ok_riscv_def |> arch_spec);
val _ = cv_auto_trans (asm_ok_riscv_def |> arch_spec);
val _ = cv_auto_trans (line_ok_light_riscv_def |> arch_spec);
val _ = cv_auto_trans (sec_ok_light_riscv_def |> arch_spec);

val pre = cv_trans_pre "" (enc_lines_again_riscv_def |> arch_spec);

Theorem enc_lines_again_riscv_pre[cv_pre,local]:
  ∀labs ffis pos v0 v. enc_lines_again_riscv_pre labs ffis pos v0 v
Proof
  Induct_on ‘v0’ \\ simp [Once pre]
QED

val pre = cv_trans_pre "" (enc_secs_again_riscv_def |> arch_spec);

Theorem enc_secs_again_riscv_pre[cv_pre,local]:
  ∀pos labs ffis v. enc_secs_again_riscv_pre pos labs ffis v
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

val pre = cv_auto_trans_pre "" (remove_labels_loop_riscv_def |> arch_spec);

Theorem remove_labels_loop_riscv_pre[cv_pre]:
  ∀clock pos init_labs ffis sec_list.
    remove_labels_loop_riscv_pre clock pos init_labs ffis sec_list
Proof
  Induct_on ‘clock’ \\ simp [Once pre]
QED

val _ = cv_trans (enc_line_riscv_def |> arch_spec);
val _ = cv_auto_trans (enc_sec_riscv_def |> arch_spec);
val _ = cv_auto_trans (enc_sec_list_riscv_def |> arch_spec);
val _ = cv_trans (remove_labels_riscv_def |> arch_spec);
val _ = cv_auto_trans (compile_lab_riscv_def |> arch_spec);
val _ = cv_trans (lab_to_target_riscv_def |> arch_spec);
val _ = cv_trans from_lab_riscv_def;

val _ = cv_trans ((from_stack_riscv_def |> arch_spec)
  |> SRULE [data_to_wordTheory.max_heap_limit_def,backend_commonTheory.word_shift_def]);

val _ = cv_auto_trans (from_word_riscv_def |> arch_spec);

val pre = cv_trans_pre "" (get_forced_riscv_def |> arch_spec);
Theorem get_forced_riscv_pre[cv_pre,local]:
  ∀v acc. get_forced_riscv_pre v acc
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ gvs [] \\ last_x_assum $ irule
  \\ gvs [wordLangTheory.prog_size_def]
QED

val _ = cv_trans (word_alloc_inlogic_riscv_def |> arch_spec);

val pre = cv_trans_pre "" (inst_select_exp_riscv_def |> arch_spec);
Theorem inst_select_exp_riscv_pre[cv_pre]:
  ∀v tar temp. inst_select_exp_riscv_pre tar temp v
Proof
  gen_tac \\ completeInduct_on ‘exp_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ rw [] \\ simp [Once pre]
  \\ rw [] \\ gvs []
  \\ last_x_assum irule
  \\ gvs [wordLangTheory.exp_size_def]
QED

val pre = cv_trans_pre "" (inst_select_riscv_def |> arch_spec);
Theorem inst_select_riscv_pre[cv_pre,local]:
  ∀v temp. inst_select_riscv_pre temp v
Proof
  gen_tac \\ completeInduct_on ‘prog_size (K 0) v’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once pre] \\ rw []
  \\ first_x_assum irule \\ gvs [wordLangTheory.prog_size_def]
QED

val pre = (each_inlogic_riscv_def |> arch_spec) |> cv_trans_pre "";
Theorem each_inlogic_riscv_pre[cv_pre,local]:
  ∀v. each_inlogic_riscv_pre v
Proof
  Induct \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans (word_to_word_inlogic_riscv_def |> arch_spec);
val _ = cv_trans (from_word_0_riscv_def |> arch_spec);

val _ = cv_trans ((compile_0_riscv_def |> arch_spec)
                    |> SRULE [data_to_wordTheory.stubs_def,
                              backend_64_cvTheory.inline,
                              to_map_compile_part]);

val _ = cv_trans (riscvBackendDefsTheory.to_word_0_riscv_def |> arch_spec);
val _ = cv_auto_trans (riscvBackendDefsTheory.to_livesets_0_riscv_def |> arch_spec);
