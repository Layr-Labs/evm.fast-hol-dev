Theory panCrepCv
Ancestors panCrepExpCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``, beta |-> ``:64``];
(* Eliminate only function-valued lets: expanding every let duplicates the
   large compiler cases and makes the totality proof needlessly expensive. *)
fun function_let_conv tm =
  case strip_comb tm of
    (c,[f,x]) =>
      if same_const c boolSyntax.let_tm andalso can dom_rng (type_of x)
      then pairLib.let_CONV tm else NO_CONV tm
  | _ => NO_CONV tm;
val compile_pre = cv_auto_trans_pre "" (spec64 pan_to_crepTheory.compile_def |> CONV_RULE (DEPTH_CONV function_let_conv));
Theorem crep_compile_pre[cv_pre]:
  !p ct. pan_to_crep_compile_pre ct (p : 64 panLang$prog)
Proof
  gen_tac >> completeInduct_on `panLang$prog_size (K 0) p` >>
  rw [] >> Cases_on `p` >> simp [Once compile_pre]
QED
Theorem mk_ctxt_cv:
  pan_to_crep$mk_ctxt v f m (e : mlstring |-> word64) =
  (context v f e m : 64 pan_to_crep$context)
Proof
  simp [pan_to_crepTheory.mk_ctxt_def, pan_to_crepTheory.context_component_equality]
QED
val _ = cv_auto_trans mk_ctxt_cv;
val _ = cv_auto_trans (alistTheory.alist_to_fmap_def
  |> INST_TYPE [alpha |-> ``:mlstring``]);
val _ = cv_auto_trans (pan_to_crepTheory.make_funcs_def
  |> INST_TYPE [alpha |-> ``:mlstring``]);
val _ = cv_auto_trans (spec64 pan_to_crepTheory.compile_to_crep_def
  |> CONV_RULE (DEPTH_CONV function_let_conv));
