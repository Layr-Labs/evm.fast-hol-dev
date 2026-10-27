(* A bounded decoder used only to generate an independently checked hint. *)
Theory decoderTreeHint
Ancestors decoderStaticHint
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
(* The generated map decoder tests positivity using subtraction from zero. *)
Theorem cv_sub_zero_positive[simp]:
  cv$c2b (cv$cv_sub v (cv$Num 0)) = (?n. v = cv$Num (SUC n))
Proof
  Cases_on `v` >> gvs [cvTheory.c2b_def] >> Cases_on `m` >> gvs []
QED
Definition treeHint_def:
  treeHint 0 c ns = ([],ns) /\
  treeHint (SUC fuel) c ns =
    if c = 0 then ([],ns) else
      case ns of [] => ([],ns) | [t] => ([],ns) | t::n::rest =>
        let (children,rest1) = treeHint fuel n rest;
            (siblings,rest2) = treeHint fuel (c-1) rest1
        in (num_tree_enc_dec$Tree t children::siblings,rest2)
End
val tree_pre = cv_auto_trans_pre "" (measure_args [0] treeHint_def);
Theorem treeHint_pre_total[cv_pre]:
  !fuel c ns. treeHint_pre fuel c ns
Proof
  Induct_on `fuel` >> rw [] >> simp [Once tree_pre] >> rw [] >> fs []
QED
Definition numTreeHint_def:
  numTreeHint ns =
    case treeHint (LENGTH ns + 1) 1 ns of
      ([],rest) => (num_tree_enc_dec$Tree 0 [],rest)
    | (t::ts,rest) => (t,rest)
End
val _ = cv_auto_trans numTreeHint_def;
(* This condition is retained, never proved or assumed by the final checker.
   Extracting a candidate from a conditional evaluation is only hint generation. *)
val agreement = ASSUME ``num_tree_enc_dec$num_tree_dec ns = numTreeHint ns``;
val rep = DB.fetch (current_theory ()) "cv_numTreeHint_thm" |> SPEC_ALL;
val rep = SUBS [SYM agreement] rep |> DISCH (concl agreement)
  |> PURE_REWRITE_RULE [GSYM cv_repTheory.cv_rep_def];
val _ = if null(hyp rep) then ignore(check_thm rep) else failwith "tree hint hypotheses";
val _ = save_thm ("numTreeHint_decoder_rep[cv_rep]",rep);
