(* Exact prefix rules for compiler configuration fields left at their preset.
   These are conditional representations, not assumed configuration facts. *)
Theory decoderStaticHint
Ancestors backend_64_cv riscv_config
Libs preamble cv_transLib recordLiteralLib
open num_list_enc_decTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun register_static name value enc dec =
  let
    val ns = ``ns : num list``
    val rest = ``rest : num list``
    val value_lit = rhs (concl (recordLiteralLib.normalize value))
    val encoded = rhs (concl (EVAL (mk_icomb (``misc$append``,mk_comb(enc,value)))))
    val len = length (fst(listSyntax.dest_list encoded))
    val n = numSyntax.term_of_int len
    val tail = listSyntax.mk_drop(n,ns)
    val pair = pairSyntax.mk_pair(value_lit,rest)
    val decoded = EVAL (mk_comb(dec,listSyntax.mk_append(encoded,rest)))
    val prefix_result = TRANS decoded (SYM (EVAL pair))
    val def = new_definition (name ^ "_def",
      mk_eq (mk_comb(mk_var(name,mk_type("fun",[``:num list``,type_of pair])),ns),
        pairSyntax.mk_pair(value_lit,tail)))
    val _ = cv_auto_trans def
    val pre = mk_eq(listSyntax.mk_take(n,ns),encoded)
    val input_eq = SYM (REWRITE_RULE [ASSUME pre] (ISPECL [n,ns] TAKE_DROP))
    val eq = TRANS (AP_TERM dec input_eq) (INST [rest |-> tail] prefix_result)
      |> REWRITE_RULE [GSYM def]
    val rep = DB.fetch (current_theory ()) ("cv_" ^ name ^ "_thm") |> SPEC_ALL
    val rep = SUBS [SYM eq] rep |> DISCH pre
      |> PURE_REWRITE_RULE [GSYM cv_repTheory.cv_rep_def]
    val _ = if same_const (fst(strip_comb(cv_miscLib.cv_rep_hol_tm(concl rep)))) dec
            then () else failwith "static decoder representation did not match"
    val _ = if null(hyp rep) then ignore(check_thm rep) else failwith "static decoder hypotheses"
    val _ = save_thm (name ^ "_decoder_rep[cv_rep]",rep)
  in () end;
val _ = register_static "sourceConfigHint" ``riscv_backend_config.source_conf``
  ``backend_enc_dec$source_to_flat_config_enc`` ``backend_enc_dec$source_to_flat_config_dec``;
val _ = register_static "closConfigHint" ``riscv_backend_config.clos_conf``
  ``backend_enc_dec$clos_to_bvl_config_enc`` ``backend_enc_dec$clos_to_bvl_config_dec``;
val _ = register_static "bvlConfigHint" ``riscv_backend_config.bvl_conf``
  ``backend_enc_dec$bvl_to_bvi_config_enc`` ``backend_enc_dec$bvl_to_bvi_config_dec``;
