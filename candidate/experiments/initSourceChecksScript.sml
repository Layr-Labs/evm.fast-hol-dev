(* Closed syntactic premises of Pancake compiler correctness for the fixed guest. *)
Theory initSourceChecks
Ancestors initPrepared pan_to_targetProof
Libs preamble cv_transLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``];
fun save_closed name th =
  if null (hyp th) then save_thm (name, check_thm th)
  else failwith (name ^ " has assumptions");
Definition distinctGuestParams_def:
  distinctGuestParams (prog : 64 panLang$decl list) =
    distinct_params (functions prog)
End
val _ = cv_auto_trans distinctGuestParams_def;
val _ = cv_auto_trans (spec64 panLangTheory.size_of_eids_def);
val _ = cv_auto_trans (spec64 panLangTheory.functions_def);
Definition distinctGuestNames_def:
  distinctGuestNames (prog : 64 panLang$decl list) =
    ALL_DISTINCT (MAP FST (functions prog))
End
val _ = cv_auto_trans distinctGuestNames_def;
val _ = save_closed "prepared_distinct_params"
  (REWRITE_RULE [distinctGuestParams_def]
    (EQT_ELIM (cv_eval ``distinctGuestParams prepared_guest``)));
val _ = save_closed "prepared_distinct_functions"
  (REWRITE_RULE [distinctGuestNames_def]
    (EQT_ELIM (cv_eval ``distinctGuestNames prepared_guest``)));
val prepared_exception_count = save_closed "prepared_exception_count"
  (cv_eval ``size_of_eids prepared_guest``);
Theorem prepared_exception_bound:
  size_of_eids prepared_guest < dimword (:64)
Proof
  simp [prepared_exception_count, wordsTheory.dimword_64]
QED

(* Eliminate the specification's unbounded quantifiers before translation. *)
Definition binaryPanop_def:
  binaryPanop (e : 64 panLang$exp) =
    case e of Panop op es => LENGTH es = 2 | _ => T
End
Theorem binaryPanop_spec:
  (\x : 64 panLang$exp. ∀op es. x = Panop op es ⇒ LENGTH es = 2) = binaryPanop
Proof
  simp [FUN_EQ_THM] >> Cases >> simp [binaryPanop_def]
QED
val _ = cv_auto_trans binaryPanop_def;
(* First-order aliases retain the original traversal, with explicit list
   recursion so cv translation needs no higher-order termination heuristic. *)
Definition binaryExp_def:
  binaryExp e = every_exp binaryPanop e
End
Definition binaryExps_def:
  binaryExps es = EVERY binaryExp es
End
Definition binaryFields_def:
  binaryFields (es : (mlstring # 64 panLang$exp) list) = EVERY (binaryExp o SND) es
End
Theorem binaryExp_eq:
  (binaryExp (Const w) = T) /\
  (binaryExp (Var vk v) = T) /\
  (binaryExp (RStruct es) = binaryExps es) /\
  (binaryExp (RField i e) = binaryExp e) /\
  (binaryExp (panLang$NStruct nm fieldExps) = binaryFields fieldExps) /\
  (binaryExp (NField fieldName e) = binaryExp e) /\
  (binaryExp (Load loadShape e) = binaryExp e) /\
  (binaryExp (Load32 e) = binaryExp e) /\
  (binaryExp (LoadByte e) = binaryExp e) /\
  (binaryExp (Op bop es) = binaryExps es) /\
  (binaryExp (Panop op es) = (LENGTH es = 2 /\ binaryExps es)) /\
  (binaryExp (Cmp c e1 e2) = (binaryExp e1 /\ binaryExp e2)) /\
  (binaryExp (Shift sh e1 e2) = (binaryExp e1 /\ binaryExp e2)) /\
  (binaryExp BaseAddr = T) /\
  (binaryExp TopAddr = T) /\
  (binaryExp BytesInWord = T) /\
  (binaryExps [] = T) /\
  (binaryExps (e::es) = (binaryExp e /\ binaryExps es)) /\
  (binaryFields [] = T) /\
  (binaryFields ((nm,e)::fieldExps) = (binaryExp e /\ binaryFields fieldExps))
Proof
  simp [binaryExp_def,binaryExps_def,binaryFields_def,
    panPropsTheory.every_exp_def,binaryPanop_def,EVERY_MAP] >>
  simp [GSYM binaryExp_def,o_DEF,ETA_AX]
QED
val binary_pre = cv_auto_trans_pre "" binaryExp_eq;
Theorem binary_pre_induction:
  (!e. binaryExp_pre e) /\
  (!es. binaryFields_pre es) /\
  (!p : mlstring # 64 panLang$exp. binaryExp_pre (SND p)) /\
  (!es. binaryExps_pre es)
Proof
  ho_match_mp_tac panLangTheory.exp_induction >>
  rw [] >> simp [Once binary_pre] >> rw [] >> fs []
QED
val _ = save_thm ("binary_pre_total[cv_pre]",
  LIST_CONJ (map (fn n => List.nth (CONJUNCTS binary_pre_induction,n)) [0,1,3]));
Theorem every_binary_eq:
  every_exp binaryPanop = binaryExp
Proof
  simp [FUN_EQ_THM,binaryExp_def]
QED
val _ = cv_auto_trans
  (PURE_REWRITE_RULE [binaryPanop_spec,every_binary_eq]
    (spec64 pan_to_wordProofTheory.good_panops_def));
val _ = cv_auto_trans (spec64 pan_to_targetProofTheory.pancake_good_code_def);
val _ = save_closed "prepared_good_code"
  (EQT_ELIM (cv_eval ``pancake_good_code prepared_guest``));
