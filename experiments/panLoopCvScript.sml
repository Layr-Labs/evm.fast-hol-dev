Theory panLoopCv
Ancestors loopPreludeCv cvInterSize
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``, beta |-> ``:64``];
fun function_let_conv tm =
  case strip_comb tm of
    (c,[f,x]) =>
      if same_const c boolSyntax.let_tm andalso can dom_rng (type_of x)
      then pairLib.let_CONV tm else NO_CONV tm
  | _ => NO_CONV tm;
val shrink_pre = cv_auto_trans_pre_rec "" (spec64 loop_liveTheory.shrink_def)
  (WF_REL_TAC
    `inv_image (measure I LEX measure I LEX measure I)
      (\x. case x of
         INL (_,c,_) => (cv$cv_size c, 0:num, 0:num)
       | INR (_,live_in,l1,l2,body) =>
           (cv$cv_size body, 1:num,
            cv$c2n (cv_std$cv_size' live_in) - cv$c2n (cv_std$cv_size' l1)))` >>
   cv_termination_tac >>
   qspecl_then [`cv_live_in`, `x2`] mp_tac cv_tree_inter_size >>
   qspec_then `cv_l1` strip_assume_tac cv_tree_size_num >>
   qspec_then `cv_inter cv_live_in x2` strip_assume_tac cv_tree_size_num >>
   qspec_then `cv_live_in` strip_assume_tac cv_tree_size_num >>
   gvs [cvTheory.cv_sub_def, cvTheory.cv_lt_def,
        cvTheory.c2b_def, cvTheory.c2n_def] >>
   Cases_on `n < n'` >> gvs [] >> decide_tac);
Theorem shrink_total[cv_pre]:
  (!lt p l. loop_live_shrink_pre lt (p : 64 loopLang$prog) l) /\
  (!lt live_in l1 l2 body.
    loop_live_fixedpoint_pre lt live_in l1 l2 (body : 64 loopLang$prog))
Proof
  ho_match_mp_tac (spec64 loop_liveTheory.shrink_ind) >>
  rw [] >> simp [Once shrink_pre] >> rw [] >> gvs []
QED
val call_pre = cv_auto_trans_pre "" (spec64 loop_callTheory.comp_def);
Theorem loop_call_total[cv_pre]:
  !p l. loop_call_comp_pre l (p : 64 loopLang$prog)
Proof
  gen_tac >> completeInduct_on `loopLang$prog_size (K 0) p` >>
  rw [] >> Cases_on `p` >> simp [Once call_pre]
QED
Theorem loop_context_cv:
  crep_to_loop$mk_ctxt target v f m =
  (context v f m target : crep_to_loop$context)
Proof
  simp [crep_to_loopTheory.mk_ctxt_def, crep_to_loopTheory.context_component_equality]
QED
val _ = cv_auto_trans loop_context_cv;
val _ = cv_auto_trans (crep_to_loopTheory.make_funcs_def
  |> INST_TYPE [alpha |-> ``:mlstring``]);
val _ = cv_auto_trans (crep_to_loopTheory.rt_var_def
  |> INST_TYPE [alpha |-> ``:num``]);
Definition lookupVars_def:
  lookupVars (m : num |-> num) vs = OPT_MMAP (FLOOKUP m) vs
End
Theorem lookupVars_eq:
  (lookupVars m [] = SOME []) /\
  (lookupVars m (v::vs) =
    case FLOOKUP m v of NONE => NONE | SOME x =>
      case lookupVars m vs of NONE => NONE | SOME xs => SOME (x::xs))
Proof
  simp [lookupVars_def, OPT_MMAP_def, optionTheory.OPTION_BIND_def] >>
  rpt CASE_TAC >> simp []
QED
val lookup_pre = cv_auto_trans_pre "" lookupVars_eq;
Theorem lookupVars_total[cv_pre]:
  !m vs. lookupVars_pre m vs
Proof
  Induct_on `vs` >> simp [Once lookup_pre] >> rw [] >> simp []
QED
Theorem lookupVars_inline[cv_inline] = GSYM lookupVars_def;
val _ = cv_auto_trans (crep_to_loopTheory.rt_vars_def
  |> INST_TYPE [alpha |-> ``:num``]);
val loop_compile_pre = cv_auto_trans_pre "" (spec64 crep_to_loopTheory.compile_def);
Theorem loop_compile_total[cv_pre]:
  !p ct l. crep_to_loop_compile_pre ct l (p : 64 crepLang$prog)
Proof
  gen_tac >> completeInduct_on `crepLang$prog_size (K 0) p` >>
  rw [] >> Cases_on `p` >> simp [Once loop_compile_pre]
QED
Definition arithExps_def:
  arithExps (es : 64 crepLang$exp list) = MAP crep_arith$simp_exp es
End
Theorem arithExps_eq:
  (arithExps [] = []) /\
  (arithExps (e::es) = crep_arith$simp_exp e :: arithExps es)
Proof
  simp [arithExps_def]
QED
Theorem arithExps_eta:
  MAP (\a. crep_arith$simp_exp a) es = arithExps es
Proof
  simp [arithExps_def, ETA_THM]
QED
val arith_pre = cv_auto_trans_pre "" (CONJ
  (REWRITE_RULE [GSYM arithExps_def, arithExps_eta] (spec64 crep_arithTheory.simp_exp_def))
  arithExps_eq);
Theorem arithExps_every:
  !es. EVERY crep_arith_simp_exp_pre es ==> arithExps_pre es
Proof
  Induct >> rw [] >> simp [Once arith_pre]
QED
Theorem arith_exp_total[cv_pre]:
  !e : 64 crepLang$exp. crep_arith_simp_exp_pre e
Proof
  ho_match_mp_tac (spec64 crep_arithTheory.simp_exp_ind) >>
  rw [] >> simp [Once arith_pre] >>
  irule arithExps_every >> fs [EVERY_MEM]
QED
Theorem arithExps_total[cv_pre]:
  !es. arithExps_pre es
Proof
  rw [] >> irule arithExps_every >> simp [EVERY_MEM, arith_exp_total]
QED
val _ = cv_auto_trans (spec64 crep_to_loopTheory.compile_prog_def
  |> CONV_RULE (DEPTH_CONV function_let_conv));
