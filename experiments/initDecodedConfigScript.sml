(* Exact metadata obtained from a checked re-encoding of an untrusted hint. *)
Theory initDecodedConfig
Ancestors initConfigNumbers decoderTreeHint
Libs preamble cv_transLib recordLiteralLib decoderHintLib
open initArtifactsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name,check_thm th)
  else failwith (name ^ " has assumptions");
Theorem decoder_pair_map_inline[cv_inline] = pairTheory.PAIR_MAP;
Theorem decoder_composition_inline[cv_inline] = combinTheory.o_DEF;
Definition configurationHint_def:
  configurationHint = FST (backend_enc_dec$backend_config_dec config_numbers)
End
(* Decoder preconditions are deliberately not used as evidence. The resulting
   term is only a candidate; the unconditional encoder check below validates it. *)
val _ = decoderHintLib.translate "initDecodedConfig" "configurationHint_def";
val hint_result = cv_eval ``configurationHint``;
val candidateConfig_def = new_definition ("candidateConfig_def",
  mk_eq (mk_var ("candidateConfig",``:backend$config``),
    rhs (concl (UNDISCH_ALL hint_result))));
val _ = cv_trans_deep_embedding recordLiteralLib.normalize candidateConfig_def;
val candidate_encoding_checked = save_closed "candidate_encoding_checked"
  (EQT_ELIM (cv_eval ``backend_enc_dec$encode_backend_config candidateConfig =
    compiledBackendConfig``));
val decoded_config = save_closed "decoded_config"
  (AP_TERM ``backend_enc_dec$decode_backend_config`` candidate_encoding_checked
    |> REWRITE_RULE [backend_enc_decTheory.encode_backend_config_thm,
         GSYM compiledConfig_def] |> SYM);
val _ = cv_trans decoded_config;
