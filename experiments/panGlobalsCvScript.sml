(* Pancake globals compilation with total cv translations. *)
Theory panGlobalsCv
Ancestors panStructsTopCv mlmapCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``];

Definition globals_exps_def:
  globals_exps ct (es : 64 panLang$exp list) =
    MAP (pan_globals$compile_exp ct) es
End
Theorem globals_exps_eq:
  (globals_exps ct [] = []) /\
  (globals_exps ct (e::es) =
    pan_globals$compile_exp ct e :: globals_exps ct es)
Proof
  simp [globals_exps_def]
QED
val globals_eqs = CONJ
  (REWRITE_RULE [ETA_THM, GSYM globals_exps_def] (spec64 pan_globalsTheory.compile_exp_def))
  globals_exps_eq;
val globals_pre = cv_auto_trans_pre "" globals_eqs;
Theorem globals_list_pre_from_every:
  !es. EVERY (pan_globals_compile_exp_pre ct) es ==> globals_exps_pre ct es
Proof
  Induct >> rw [] >> simp [Once globals_pre]
QED
Theorem globals_exp_pre[cv_pre]:
  !ct e. pan_globals_compile_exp_pre ct (e : 64 panLang$exp)
Proof
  ho_match_mp_tac (spec64 pan_globalsTheory.compile_exp_ind) >>
  rw [] >> simp [Once globals_pre] >>
  irule globals_list_pre_from_every >> fs [EVERY_MEM]
QED
Theorem globals_list_pre[cv_pre]:
  !ct es. globals_exps_pre ct es
Proof
  rw [] >> irule globals_list_pre_from_every >> simp [EVERY_MEM, globals_exp_pre]
QED

Definition var_exps_def:
  var_exps (es : 64 panLang$exp list) = MAP panLang$var_exp es
End
Definition var_fields_def:
  var_fields (fs : (mlstring # 64 panLang$exp) list) = MAP panLang$var_exp (MAP SND fs)
End
Theorem var_exps_eq:
  (var_exps [] = []) /\
  (var_exps (e::es) = panLang$var_exp e :: var_exps es)
Proof
  simp [var_exps_def]
QED
Theorem var_fields_eq:
  (var_fields [] = []) /\
  (var_fields ((n,e)::fs) = panLang$var_exp e :: var_fields fs)
Proof
  simp [var_fields_def]
QED
val var_eqs = LIST_CONJ [
  REWRITE_RULE [ETA_THM, GSYM var_fields_def, GSYM var_exps_def]
    (spec64 panLangTheory.var_exp_def), var_exps_eq, var_fields_eq];
val var_pre = cv_auto_trans_pre "" var_eqs;
Theorem var_exps_pre_every:
  !es. EVERY panLang_var_exp_pre es ==> var_exps_pre es
Proof
  Induct >> rw [] >> simp [Once var_pre]
QED
Theorem var_fields_pre_every:
  !fs. EVERY (panLang_var_exp_pre o SND) fs ==> var_fields_pre fs
Proof
  Induct >> rw [] >> simp [Once var_pre] >> rw [] >> gvs []
QED
Theorem var_exp_pre[cv_pre]:
  !e : 64 panLang$exp. panLang_var_exp_pre e
Proof
  ho_match_mp_tac (spec64 panLangTheory.var_exp_ind) >>
  rw [] >> simp [Once var_pre] >>
  ((irule var_exps_pre_every >> fs [EVERY_MEM]) ORELSE
   (irule var_fields_pre_every >> fs [EVERY_MEM, MEM_MAP, FORALL_PROD] >>
    metis_tac [pairTheory.SND]))
QED
Theorem var_lists_pre[cv_pre]:
  (!es. var_exps_pre es) /\ (!fs. var_fields_pre fs)
Proof
  conj_tac >> gen_tac >>
  ((irule var_exps_pre_every >> simp [EVERY_MEM, var_exp_pre]) ORELSE
   (irule var_fields_pre_every >> simp [EVERY_MEM, var_exp_pre]))
QED

val _ = cv_auto_trans (spec64 panLangTheory.shape_val_def);
val globals_stmt_pre = cv_auto_trans_pre "" (spec64 pan_globalsTheory.compile_def);
Theorem globals_compile_pre[cv_pre]:
  !ct p. pan_globals_compile_pre ct (p : 64 panLang$prog)
Proof
  ho_match_mp_tac (spec64 pan_globalsTheory.compile_ind) >>
  rw [] >> simp [Once globals_stmt_pre] >> rw [] >> gvs []
QED
Definition shape_sizes_def:
  shape_sizes ss = MAP panLang$size_of_shape ss
End
Theorem shape_sizes_eq:
  (shape_sizes [] = []) /\
  (shape_sizes (s::ss) = panLang$size_of_shape s :: shape_sizes ss)
Proof
  simp [shape_sizes_def]
QED
val sizes_pre = cv_auto_trans_pre "" (CONJ
  (REWRITE_RULE [ETA_THM, GSYM shape_sizes_def] panLangTheory.size_of_shape_def)
  shape_sizes_eq);
Theorem shape_sizes_pre_every:
  !ss. EVERY panLang_size_of_shape_pre ss ==> shape_sizes_pre ss
Proof
  Induct >> rw [] >> simp [Once sizes_pre]
QED
Theorem size_of_shape_pre[cv_pre]:
  !s. panLang_size_of_shape_pre s
Proof
  ho_match_mp_tac panLangTheory.size_of_shape_ind >>
  rw [] >> simp [Once sizes_pre] >>
  irule shape_sizes_pre_every >> fs [EVERY_MEM]
QED
Theorem shape_sizes_pre[cv_pre]:
  !ss. shape_sizes_pre ss
Proof
  rw [] >> irule shape_sizes_pre_every >> simp [EVERY_MEM, size_of_shape_pre]
QED

val globals_decs_pre = cv_auto_trans_pre "" (spec64 pan_globalsTheory.compile_decs_def);
Theorem globals_declarations_pre[cv_pre]:
  !ds ct. pan_globals_compile_decs_pre ct (ds : 64 panLang$decl list)
Proof
  Induct >> rw [] >> simp [Once globals_decs_pre]
QED

Theorem globals_context_literal:
  (<|globals := g; globals_size := n; max_globals_size := m|> : 64 pan_globals$context) =
  context g n m
Proof
  simp [pan_globalsTheory.context_component_equality]
QED
Theorem globals_function_literal:
  (<|name := n; inline := i; export := e; params := ps; body := b; return := r|> : 64 panLang$fun_decl) =
  fun_decl n i e ps b r
Proof
  simp [panLangTheory.fun_decl_component_equality]
QED

val _ = cv_auto_trans (spec64 pan_globalsTheory.compile_top_def
  |> REWRITE_RULE [globals_context_literal, globals_function_literal]);
