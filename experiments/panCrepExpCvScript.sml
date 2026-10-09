Theory panCrepExpCv
Ancestors panGlobalsCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``, beta |-> ``:64``];
val fmap_pre = finite_mapTheory.FUPDATE_LIST_THM
 |> SRULE [FORALL_PROD]
 |> INST_TYPE [alpha |-> ``:mlstring``]
 |> cv_trans_pre "mlmap_updates_pre";
Theorem mlmap_updates_pre[cv_pre]:
  !f ls. mlmap_updates_pre f ls
Proof
  Induct_on `ls` >> rw [Once fmap_pre]
QED
val _ = cv_auto_trans (pan_to_crepTheory.make_vmap_def
  |> INST_TYPE [alpha |-> ``:mlstring``]);
Definition crep_exps_def:
  crep_exps (ct : 64 pan_to_crep$context) (es : 64 panLang$exp list) =
    MAP (pan_to_crep$compile_exp ct) es
End
Theorem crep_exps_eq:
  (crep_exps ct [] = []) /\
  (crep_exps ct (e::es) =
    pan_to_crep$compile_exp ct e :: crep_exps ct es)
Proof
  simp [crep_exps_def]
QED
val crep_eqs = CONJ
  (REWRITE_RULE [ETA_THM, GSYM crep_exps_def] (spec64 pan_to_crepTheory.compile_exp_def))
  crep_exps_eq;
val crep_pre = cv_auto_trans_pre "" crep_eqs;
Theorem crep_list_pre_from_every:
  !es. EVERY (pan_to_crep_compile_exp_pre ct) es ==> crep_exps_pre ct es
Proof
  Induct >> rw [] >> simp [Once crep_pre]
QED
Theorem crep_exp_pre[cv_pre]:
  !ct e. pan_to_crep_compile_exp_pre ct (e : 64 panLang$exp)
Proof
  ho_match_mp_tac (spec64 pan_to_crepTheory.compile_exp_ind) >>
  rw [] >> simp [Once crep_pre] >>
  irule crep_list_pre_from_every >> fs [EVERY_MEM]
QED
Theorem crep_list_pre[cv_pre]:
  !ct es. crep_exps_pre ct es
Proof
  rw [] >> irule crep_list_pre_from_every >> simp [EVERY_MEM, crep_exp_pre]
QED


Definition crep_vars_def:
  crep_vars (es : 64 crepLang$exp list) = MAP crepLang$var_cexp es
End
Theorem crep_vars_eq:
  (crep_vars [] = []) /\
  (crep_vars (e::es) = crepLang$var_cexp e :: crep_vars es)
Proof
  simp [crep_vars_def]
QED
val cvar_pre = cv_auto_trans_pre "" (CONJ
  (REWRITE_RULE [ETA_THM, GSYM crep_vars_def] (spec64 crepLangTheory.var_cexp_def))
  crep_vars_eq);
Theorem crep_vars_every:
  !es. EVERY crepLang_var_cexp_pre es ==> crep_vars_pre es
Proof
  Induct >> rw [] >> simp [Once cvar_pre]
QED
Theorem crep_var_pre[cv_pre]:
  !e : 64 crepLang$exp. crepLang_var_cexp_pre e
Proof
  ho_match_mp_tac (spec64 crepLangTheory.var_cexp_ind) >>
  rw [] >> simp [Once cvar_pre] >>
  irule crep_vars_every >> fs [EVERY_MEM]
QED
Theorem crep_vars_pre[cv_pre]:
  !es. crep_vars_pre es
Proof
  rw [] >> irule crep_vars_every >> simp [EVERY_MEM, crep_var_pre]
QED

val _ = cv_auto_trans (pan_to_crepTheory.exp_hdl_def
  |> INST_TYPE [alpha |-> ``:64``, beta |-> ``:mlstring``, gamma |-> ``:panLang$shape``]);
val _ = cv_auto_trans (spec64 crepLangTheory.nested_decs_def);
