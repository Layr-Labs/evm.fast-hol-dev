Theory panWordCv
Ancestors panLoopCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val spec64 = INST_TYPE [alpha |-> ``:64``, beta |-> ``:64``];
Definition wordExps_def:
  wordExps ct (es : 64 loopLang$exp list) = MAP (loop_to_word$comp_exp ct) es
End
Theorem wordExps_eq:
  (wordExps ct [] = []) /\
  (wordExps ct (e::es) = loop_to_word$comp_exp ct e :: wordExps ct es)
Proof
  simp [wordExps_def]
QED
Theorem wordExps_eta:
  MAP (\a. loop_to_word$comp_exp ct a) es = wordExps ct es
Proof
  rewrite_tac [wordExps_def, ETA_THM]
QED
val exp_pre = cv_auto_trans_pre "" (CONJ
  (REWRITE_RULE [GSYM wordExps_def, wordExps_eta] (spec64 loop_to_wordTheory.comp_exp_def))
  wordExps_eq);
Theorem wordExps_every:
  !es. EVERY (loop_to_word_comp_exp_pre ct) es ==> wordExps_pre ct es
Proof
  Induct >> rw [] >> simp [Once exp_pre]
QED
Theorem word_exp_total[cv_pre]:
  !ct e. loop_to_word_comp_exp_pre ct (e : 64 loopLang$exp)
Proof
  ho_match_mp_tac (spec64 loop_to_wordTheory.comp_exp_ind) >>
  rw [] >> simp [Once exp_pre] >>
  irule wordExps_every >> fs [EVERY_MEM]
QED
Theorem wordExps_total[cv_pre]:
  !ct es. wordExps_pre ct es
Proof
  rw [] >> irule wordExps_every >> simp [EVERY_MEM, word_exp_total]
QED
val word_pre = cv_auto_trans_pre "" (spec64 loop_to_wordTheory.comp_def);
Theorem word_compile_total[cv_pre]:
  !p ct l. loop_to_word_comp_pre ct (p : 64 loopLang$prog) l
Proof
  gen_tac >> completeInduct_on `loopLang$prog_size (K 0) p` >>
  rw [] >> Cases_on `p` >> simp [Once word_pre] >>
  rw [] >> gvs [] >> CCONTR_TAC >> gvs []
QED
val _ = cv_auto_trans (spec64 loop_to_wordTheory.compile_def);
