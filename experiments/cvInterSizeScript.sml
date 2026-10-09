(* Cardinality monotonicity for cv's sptree intersection, including malformed
   cv values; needed by liveness fixed-point termination. *)
Theory cvInterSize
Ancestors cv_std
Libs preamble
val size_def = DB.fetch "cv_std" "cv_size'_def";
val inter_def = DB.fetch "cv_std" "cv_inter_def";
val inter_ind = DB.fetch "cv_std" "cv_inter_ind";
val bn_def = DB.fetch "cv_std" "cv_mk_BN_def";
val bs_def = DB.fetch "cv_std" "cv_mk_BS_def";
val cv_simps = [cvTheory.cv_if_def, cvTheory.cv_ispair_def,
  cvTheory.cv_fst_def, cvTheory.cv_snd_def, cvTheory.cv_lt_def,
  cvTheory.c2b_def, cvTheory.c2n_def, cvTheory.cv_add_def,
  cvTheory.cv_eq_def];
Theorem cv_tree_sizes[simp]:
  (cv_std$cv_size' (cv$Num n) = cv$Num 0) /\
  (cv_std$cv_size' (cv$Pair (cv$Num 1) x) = cv$Num 1) /\
  (cv_std$cv_size' (cv$Pair (cv$Num 2) (cv$Pair x y)) =
    cv_add (cv_std$cv_size' x) (cv_std$cv_size' y)) /\
  (cv_std$cv_size' (cv$Pair (cv$Num 3) (cv$Pair x (cv$Pair v y))) =
    cv_add (cv_add (cv_std$cv_size' x) (cv_std$cv_size' y)) (cv$Num 1))
Proof
  rpt conj_tac >> CONV_TAC (LAND_CONV (REWR_CONV size_def)) >> simp cv_simps
QED
Theorem cv_add_num:
  !x y. ?n. cv_add x y = cv$Num n
Proof
  Cases >> Cases >> simp [cvTheory.cv_add_def]
QED
Theorem cv_tree_size_num:
  !x. ?n. cv_std$cv_size' x = cv$Num n
Proof
  gen_tac >> once_rewrite_tac [size_def] >>
  simp [cvTheory.cv_if_def] >> rpt CASE_TAC >> simp [cv_add_num]
QED
Theorem cv_tree_add_sizes[simp]:
  cv_add (cv_std$cv_size' x) (cv_std$cv_size' y) =
  cv$Num (cv$c2n (cv_std$cv_size' x) + cv$c2n (cv_std$cv_size' y))
Proof
  qspec_then `x` strip_assume_tac cv_tree_size_num >>
  qspec_then `y` strip_assume_tac cv_tree_size_num >> simp cv_simps
QED
Theorem cv_tree_size_mk_bn[simp]:
  cv$c2n (cv_std$cv_size' (cv_std$cv_mk_BN x y)) =
  cv$c2n (cv_std$cv_size' x) + cv$c2n (cv_std$cv_size' y)
Proof
  simp ([bn_def] @ cv_simps) >> rw [] >> gvs cv_simps
QED
Theorem cv_tree_size_mk_bs[simp]:
  cv$c2n (cv_std$cv_size' (cv_std$cv_mk_BS x v y)) =
  cv$c2n (cv_std$cv_size' x) + cv$c2n (cv_std$cv_size' y) + 1
Proof
  simp ([bs_def] @ cv_simps) >> rw [] >> gvs cv_simps
QED
Theorem cv_tree_inter_size:
  !x y. cv$c2n (cv_std$cv_size' (cv_std$cv_inter x y)) <=
        cv$c2n (cv_std$cv_size' x)
Proof
  ho_match_mp_tac inter_ind >> rw [] >>
  once_rewrite_tac [inter_def] >> simp cv_simps >> rw [] >>
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV size_def))) >>
  gvs cv_simps >> decide_tac
QED
