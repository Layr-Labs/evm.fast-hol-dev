(* Standard-kernel replay of a separately produced proof article. *)
load "strictReplayLib";
open HolKernel boolLib bossLib;
val _ = PolyML.print_depth 0;
val fixed = "OpenTheoryReaderContext" :: "cv_type" :: ancestry "cv_type";
val trusted = strictReplayLib.kernel_axioms @ List.concat (map (fn thy => map snd (DB.definitions thy @ DB.theorems thy)) fixed);
val _ = new_theory "candidateCertificate";
val reader = strictReplayLib.reader trusted;
val reader = {const_name= #const_name reader, tyop_name= #tyop_name reader,
 define_const= #define_const reader, define_tyop= #define_tyop reader,
 axiom=fn proved => fn seq as (hs,c) => (#axiom reader proved seq handle e => (print (term_to_string c ^ "\n"); raise e))};
val proved = articleReaderLib.raw_read_article
  (TextIO.openIn "cv-smoke.art") reader;
val expected = ``smoke (cv$Num 10) = cv$Num 17``;
val _ = case List.find (strictReplayLib.same_sequent ([],expected)) (Net.listItems proved) of
  SOME th => (strictReplayLib.checked th; print "REPLAY_SMOKE_OK\n")
| NONE => raise Fail "missing smoke result";

val decoded_expected = ``cv_type$to_list (cv_type$to_word : cv -> word8)
  (cv$Pair (cv$Num 0) (cv$Pair (cv$Num 255) (cv$Pair (cv$Num 17) (cv$Num 0)))) =
  [0w;255w;17w]``;
val _ = case List.find (strictReplayLib.same_sequent ([],decoded_expected)) (Net.listItems proved) of
  SOME th => (strictReplayLib.checked th; print "LITERAL_DECODE_REPLAY_OK\n")
| NONE => raise Fail "missing literal decoding proof";

val named_literal = prim_mk_const {Thy="candidateCertificate",Name="smokeBytes"};
val named_expected = mk_eq (lhs decoded_expected,named_literal);
val _ = case List.find (strictReplayLib.same_sequent ([],named_expected)) (Net.listItems proved) of
  SOME th => (strictReplayLib.checked th; print "LITERAL_REQUEST_REPLAY_OK\n")
| NONE => raise Fail "missing recomputed literal binding";

val eager_expected = ``(p:bool) ==> p``;
val _ = case List.find (strictReplayLib.same_sequent ([],eager_expected)) (Net.listItems proved) of
  SOME th => ignore (strictReplayLib.checked th)
| NONE => raise Fail "missing eager subgoal proof";

val dotted_constant = prim_mk_const {Thy="candidateCertificate",Name="helper.with.dots"};
val dotted_expected = mk_eq(dotted_constant,``cv$Num 19``);
val _ = case List.find (strictReplayLib.same_sequent ([],dotted_expected)) (Net.listItems proved) of
  SOME th => ignore (strictReplayLib.checked th)
| NONE => raise Fail "logical constant name changed during binding sanitization";
