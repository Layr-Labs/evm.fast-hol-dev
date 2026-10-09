Theory panStructsTopCv
Ancestors panStructsCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``];

val structs_pre = cv_auto_trans_pre "" (spec64 pan_structsTheory.compile_def);
Theorem structs_compile_pre[cv_pre]:
  !ct p. pan_structs_compile_pre ct (p : 64 panLang$prog)
Proof
  ho_match_mp_tac (spec64 pan_structsTheory.compile_ind) >>
  rw [] >> simp [Once structs_pre] >> rw [] >> gvs [] >>
  Cases_on `ctxt` >> gvs [pan_structsTheory.context_fn_updates]
QED

val decs_pre = cv_auto_trans_pre "" (spec64 pan_structsTheory.compile_decs_def);
Theorem structs_decs_pre[cv_pre]:
  !ds ct. pan_structs_compile_decs_pre ct (ds : 64 panLang$decl list)
Proof
  Induct >> rw [] >> simp [Once decs_pre]
QED

val names_pre = cv_auto_trans_pre "" (spec64 pan_structsTheory.get_names_def);
Theorem structs_names_pre[cv_pre]:
  !ds ct. pan_structs_get_names_pre ct (ds : 64 panLang$decl list)
Proof
  Induct >> rw [] >> simp [Once names_pre]
QED

val _ = cv_auto_trans (spec64 pan_structsTheory.compile_top_def);
