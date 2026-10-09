(* Author-side proof binding. The verifier independently creates the same
   literals from its frozen snapshot and accepts only their exact Certificate. *)
open HolKernel boolLib bossLib;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val rom_path = valOf (OS.Process.getEnv "HOL_INIT_E_ROM");
val article_path = valOf (OS.Process.getEnv "HOL_INIT_E_BINDING_ARTICLE");
val binary = BinIO.openIn rom_path;
val rom = BinIO.inputAll binary;
val _ = BinIO.closeIn binary;
val bytes = listSyntax.mk_list
  (Word8Vector.foldr (fn (b,rest) => wordsSyntax.mk_wordii (Word8.toInt b,8)::rest) [] rom,
   ``:word8``);
val _ = new_theory "submissionLiterals";
val submittedBytes_def = new_definition ("submittedBytes_def",
  mk_eq (mk_var ("submittedBytes",``:word8 list``),bytes));
val submittedScore_def = new_definition ("submittedScore_def",
  mk_eq (mk_var ("submittedScore",``:initParams$budget``),``initParams$Infinity``));
(* These premises must match the verifier-created literals, so export them as
   requests for those fixed definitions, never as candidate definitions. *)
val _ = Thm.delete_proof submittedBytes_def;
val _ = Thm.delete_proof submittedScore_def;
val _ = new_theory "baselineLiteralBinding";
val _ = Logging.raw_start_logging [] (TextIO.openOut article_path);
val rom_raw = cv_transLib.cv_eval_raw ``initBaselineRom$baselineRom``;
val _ = print "BASELINE_ROM_CV_COMPUTED\n";
val decoded = literalDecodeLib.decode (rand (rhs (concl rom_raw)));
val _ = print "BASELINE_LITERAL_DECODED\n";
val rom_result = TRANS rom_raw decoded;
val _ = if aconv (rhs (concl rom_result)) bytes then ()
        else raise Fail "baseline ROM differs from frozen author bytes";
val literal_encoding = TRANS decoded (SYM submittedBytes_def);
(* The strict reader re-proves this conversion from its own sanitized literal.
   Export the request instead of nearly a million primitive decoding steps. *)
val _ = Thm.delete_proof literal_encoding;
val bytes_eq = TRANS rom_raw literal_encoding;
val score_eq = SYM submittedScore_def;
val certificate_const = prim_mk_const {Thy="initChallenge",Name="Certificate"};
val conclusion_eq = MK_COMB (AP_TERM certificate_const bytes_eq,score_eq);
val result = EQ_MP conclusion_eq initBaselineCertificateTheory.baseline_certificate;
val expected = list_mk_comb (certificate_const,
  [lhs(concl submittedBytes_def),lhs(concl submittedScore_def)]);
val _ = if null(hyp result) andalso aconv (concl result) expected andalso
   (Tag.isEmpty (Thm.tag result) orelse Tag.isDisk (Thm.tag result))
   then () else raise Fail "literal binding did not prove the exact Certificate";
val _ = Logging.export_thm result;
val _ = Logging.stop_logging ();
val _ = print "BASELINE_LITERAL_BINDING_OK\n";
