(* Experimental translation beyond the simplifier; not in the default build. *)
Theory panStructsCv
Ancestors panSimplifyCv pan_to_word
Libs preamble cv_transLib

val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``];
(* Register the mutually recursive shape/shape-list equations together. *)
val shape_pre = cv_auto_trans_pre_rec "" pan_structsTheory.compile_shape_def
  (WF_REL_TAC
     `inv_image (measure cv$cv_size LEX measure cv$cv_size)
        (\x. case x of INL p => p | INR p => p)` >>
   (fn g => let
      val d = DB.fetch (current_theory ()) "cv_dropWhile_lam_pair_CASE_lam_la_def"
      val bound = prove (
        ``!x y. cv_size (cv_dropWhile_lam_pair_CASE_lam_la x y) <= cv_size x``,
        Induct >> simp [Once d, cvTheory.cv_if_def, cvTheory.cv_ispair_def,
          cvTheory.cv_fst_def, cvTheory.cv_snd_def, cvTheory.cv_size_def] >>
        rw [] >> first_x_assum (qspec_then `y` mp_tac) >> decide_tac)
    in (cv_termination_tac >>
        qspecl_then [`cv_sctxt`, `x2`] mp_tac bound >>
        gvs [cvTheory.cv_size_def] >> decide_tac) g end));

Theorem compile_shape_pre[cv_pre]:
  (!ct : (mlstring # ('a # shape) list) list. !s. pan_structs_compile_shape_pre ct s) /\
  (!ct : (mlstring # ('a # shape) list) list. !ss. pan_structs_compile_shapes_pre ct ss)
Proof
  ho_match_mp_tac pan_structsTheory.compile_shape_ind >>
  rw [] >> simp [Once shape_pre] >> rw [] >> fs [] >> first_x_assum irule >> qexists_tac `v0'` >>
  fs [pairTheory.pair_CASE_def, ELIM_UNCURRY]
QED

val _ = cv_auto_trans (spec64 pan_structsTheory.old_exp_shape_def);
val _ = cv_auto_trans (spec64 pan_structsTheory.compile_exp_def);
