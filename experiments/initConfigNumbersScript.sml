(* Inspect the exact compiled target layout before constructing its submission. *)
Theory initConfigNumbers
Ancestors initArtifacts
Libs preamble cv_transLib recordLiteralLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name,check_thm th)
  else failwith (name ^ " has assumptions");
(* Candidate decoding is an untrusted hint. Its complete re-encoding is
   checked against the exact saved compiler result before it is used. *)
val encoded = cv_eval_raw ``compiledBackendConfig``;
val _ = check_thm encoded;
fun candidate_nums tm acc digit_scale digits =
  if cvSyntax.is_cv_pair tm then
    let val (c,rest) = cvSyntax.dest_cv_pair tm
        val d = numSyntax.int_of_term (cvSyntax.dest_cv_num c) - 32
        val _ = if 0 <= d andalso d < 60 then () else failwith "invalid config byte"
        val value = Arbnum.+ (acc,Arbnum.* (digit_scale,Arbnum.fromInt (d mod 30)))
    in if d < 30 then candidate_nums rest Arbnum.zero Arbnum.one (value::digits)
       else candidate_nums rest value (Arbnum.* (digit_scale,Arbnum.fromInt 30)) digits
    end
  else if aconv tm (cvSyntax.mk_cv_num numSyntax.zero_tm) andalso
          digit_scale = Arbnum.one then rev digits
  else failwith "incomplete configuration encoding";
val nums = candidate_nums (rand (rconc encoded)) Arbnum.zero Arbnum.one [];
val _ = print ("Configuration candidate has " ^ Int.toString (length nums) ^ " numbers\n");
val config_numbers_def = new_definition ("config_numbers_def",
  mk_eq (mk_var ("config_numbers",``:num list``),
    listSyntax.mk_list (map numSyntax.mk_numeral nums,``:num``)));
val _ = cv_trans_deep_embedding EVAL config_numbers_def;
val encoding_checked = save_closed "encoding_checked"
  (EQT_ELIM (cv_eval ``rev_nums_to_chars (REVERSE config_numbers) [] = compiledBackendConfig``));
val encoding_checked = REWRITE_RULE
  [num_list_enc_decTheory.rev_nums_to_chars_thm,listTheory.REVERSE_REVERSE,
   listTheory.APPEND_NIL] encoding_checked;
val decoded_numbers = save_closed "decoded_numbers"
  (GSYM (AP_TERM ``num_list_enc_dec$chars_to_nums`` encoding_checked)
   |> REWRITE_RULE [num_list_enc_decTheory.chars_to_nums_nums_to_chars]);
