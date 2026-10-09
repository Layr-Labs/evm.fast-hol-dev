Theory loopPreludeCv
Ancestors panCrepCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``, beta |-> ``:64``];
val _ = cv_auto_trans (crep_to_loopTheory.make_vmap_def
  |> INST_TYPE [alpha |-> ``:num``]);
fun function_let_conv tm =
  case strip_comb tm of
    (c,[f,x]) =>
      if same_const c boolSyntax.let_tm andalso can dom_rng (type_of x)
      then pairLib.let_CONV tm else NO_CONV tm
  | _ => NO_CONV tm;
val exp_pre = cv_auto_trans_pre "" (spec64 crep_to_loopTheory.compile_exp_def);
Theorem loop_exp_pre[cv_pre]:
  (!ct n l e. crep_to_loop_compile_exp_pre ct n l (e : 64 crepLang$exp)) /\
  (!ct n l es. crep_to_loop_compile_exps_pre ct n l (es : 64 crepLang$exp list))
Proof
  ho_match_mp_tac (spec64 crep_to_loopTheory.compile_exp_ind) >>
  rw [] >> simp [Once exp_pre] >> rw [] >> gvs []
QED
val live_exp_pre = cv_auto_trans_pre "" (spec64 loop_liveTheory.vars_of_exp_def);
Theorem loop_vars_pre[cv_pre]:
  (!e l. loop_live_vars_of_exp_pre (e : 64 loopLang$exp) l) /\
  (!es l. loop_live_vars_of_exp_list_pre (es : 64 loopLang$exp list) l)
Proof
  ho_match_mp_tac (spec64 loop_liveTheory.vars_of_exp_ind) >>
  rw [] >> simp [Once live_exp_pre] >> rw [] >> gvs []
QED
val mark_pre = cv_auto_trans_pre "" (spec64 loop_liveTheory.mark_all_def);
Theorem loop_mark_pre[cv_pre]:
  !p : 64 loopLang$prog. loop_live_mark_all_pre p
Proof
  gen_tac >> completeInduct_on `loopLang$prog_size (K 0) p` >>
  rw [] >> Cases_on `p` >> simp [Once mark_pre]
QED
