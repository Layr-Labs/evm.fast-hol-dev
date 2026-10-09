(* The expected proposition is constructed here, never supplied by the article.
   Load the operator-built initChallenge and sanitized submissionLiterals first. *)
structure certificateReplayLib =
struct
open HolKernel boolLib bossLib;
fun constant thy name = prim_mk_const {Thy=thy,Name=name};
fun expected () = list_mk_comb (constant "initChallenge" "Certificate",
  [constant "submissionLiterals" "submittedBytes",
   constant "submissionLiterals" "submittedScore"]);
fun replay input =
  let
    val fixed_theories = "OpenTheoryReaderContext" :: "initProofLibrary" :: ancestry "initProofLibrary";
    val literal_facts = DB.definitions "submissionLiterals";
    val fixed_facts = List.concat (map (fn thy =>
      DB.definitions thy @ DB.theorems thy) fixed_theories);
    val trusted = strictReplayLib.kernel_axioms @ map snd (literal_facts @ fixed_facts);
    val statement = expected ();
    val _ = new_theory "candidateCertificate";
    val result = strictReplayLib.read trusted statement input;
  in if null (hyp result) andalso aconv (concl result) statement then result
     else raise Fail "certificate conclusion changed"
  end;
end
