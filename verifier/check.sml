(* This fixed script reads data, constructs literals and checks a proof article.
   It never loads or evaluates participant ML or participant theory files. *)
val _ = let
open HolKernel boolLib bossLib;
(* Literal theories may contain megabytes of bytes; HTML is not a proof artifact. *)
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val snapshot = valOf (OS.Process.getEnv "HOL_INIT_E_SNAPSHOT");
fun path name = OS.Path.concat (snapshot,name);
val _ = new_theory "submissionLiterals";
val binary = BinIO.openIn (path "rom.bin");
val rom = BinIO.inputAll binary;
val _ = BinIO.closeIn binary;
val bytes = listSyntax.mk_list
  (Word8Vector.foldr (fn (b,rest) => wordsSyntax.mk_wordii (Word8.toInt b,8)::rest) [] rom,
   ``:word8``);
val submittedBytes_def = new_definition ("submittedBytes_def",
  mk_eq (mk_var ("submittedBytes",``:word8 list``),bytes));
val score_file = TextIO.openIn (path "score.txt");
val score = TextIO.inputAll score_file;
val _ = TextIO.closeIn score_file;
val budget = if score = "infinity" then ``initParams$Infinity`` else
  if size score > 0 andalso List.all Char.isDigit (String.explode score) then
    mk_comb (``initParams$Finite``,numSyntax.mk_numeral (Arbnum.fromString score))
  else raise Fail "invalid sanitized score";
val submittedScore_def = new_definition ("submittedScore_def",
  mk_eq (mk_var ("submittedScore",``:initParams$budget``),budget));
val article = TextIO.openIn (path "certificate.art");
val certificate = certificateReplayLib.replay article;
val _ = TextIO.closeIn article;
val marker = TextIO.openOut (path "verified");
val _ = TextIO.output (marker,"VERIFIED\n");
val _ = TextIO.closeOut marker;

in OS.Process.exit OS.Process.success end;
