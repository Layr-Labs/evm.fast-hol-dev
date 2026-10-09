(* Numeric specialization of CakeML's mergesort CV proof.
   CakeML-derived portions are covered by ../CAKEML-LICENSE. *)
Theory numSortCv
Ancestors backend_cv mergesort mllist
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val tm = ``$< : num -> num -> bool``;
Definition sort_num_def:
  sort_num ls =
    sort ^tm ls
End

Definition merge_tail_num_def:
  merge_tail_num b ls accl accr =
    merge_tail b ^tm ls accl accr
End

val merge_tail_eq = merge_tail_def
            |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
            |> Q.GEN ‘R’ |> ISPEC tm |> SRULE [GSYM merge_tail_num_def]
            |> GEN_ALL |> SRULE [FORALL_PROD] |> SPEC_ALL

val pre = cv_trans_pre "" merge_tail_eq;

Theorem merge_tail_num_pre[cv_pre]:
  ∀negate v0 v acc. merge_tail_num_pre negate v0 v acc
Proof
  Induct_on`v` \\ rw[]
  >- simp[Once pre]
  \\ qid_spec_tac`acc`
  \\ Induct_on`v0` \\ rw[]
  >- simp[Once pre]
  \\ simp[Once pre]
  \\ rw[]
  \\ metis_tac[]
QED

Definition mergesortN_tail_num_def:
  mergesortN_tail_num b n ls =
    mergesortN_tail b ^tm n ls
End

val mergesortN_tail_eq = mergesortN_tail_def
            |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
            |> Q.GEN ‘R’ |> ISPEC tm |> SRULE [GSYM mergesortN_tail_num_def, GSYM merge_tail_num_def]
            |> GEN_ALL |> SRULE [FORALL_PROD] |> SPEC_ALL;

Theorem c2b_b2c[local]:
  cv$c2b (b2c b) = b
Proof
  fs[cvTheory.b2c_if,cvTheory.c2b_def]
  \\ rw[]
QED

val div2_cv = backend_cvTheory.cv_arithmetic_DIV2_thm;

val pre = cv_auto_trans_pre_rec "" mergesortN_tail_eq
  (WF_REL_TAC ‘measure (cv_size o FST o SND)’ \\ rw []
   \\ rename1`_ < cv_size cvv`
   \\ Cases_on`cvv`
   \\ simp[GSYM div2_cv]
   \\ rw[DIV2_def]
   \\ cv_termination_tac
   \\ fs[c2b_b2c]
   \\ intLib.ARITH_TAC);

Theorem mergesortN_tail_num_pre[cv_pre]:
  ∀negate n l. mergesortN_tail_num_pre negate n l
Proof
  completeInduct_on`n`>>
  rw[Once pre,DIV2_def]>>
  first_x_assum irule>>
  intLib.ARITH_TAC
QED

val pre = cv_auto_trans (sort_num_def |> SRULE [sort_def,mergesort_tail_def,GSYM mergesortN_tail_num_def]);


Theorem sort_num_inline[cv_inline] = GSYM sort_num_def;
