(* Check every aligned instruction word in the fixed bootstrap image. *)
Theory initBootstrapRestricted
Ancestors initBootstrap initRestrictedStep
Libs preamble cv_transLib wordsLib bitstringLib
open initBootstrapTheory initTargetTheory wordsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition bootstrapWords_def:
  bootstrapWords = GENLIST (\i.
    byte$word_of_bytes F (0w:word32) (TAKE 4 (DROP (4*i) bootstrapBytes)))
    (LENGTH bootstrapBytes DIV 4)
End
val bootstrap_literal = cv_eval ``bootstrapBytes``;
val words_literal = CONV_RULE
  (RAND_CONV (REWRITE_CONV [bootstrap_literal] THENC EVAL)) bootstrapWords_def;
val _ = save_thm ("bootstrap_words",check_thm words_literal);
val decode_conv = computeLib.compset_conv wordsLib.words_compset
  [computeLib.Defs (supported_instruction_def :: map snd (DB.definitions "riscv")),
   computeLib.Extenders [bitstringLib.add_bitstring_compset]];
Theorem bootstrap_words_supported:
  EVERY (\w. supported_instruction (riscv$Decode w)) bootstrapWords
Proof
  rewrite_tac [words_literal] >> CONV_TAC decode_conv >>
  CONV_TAC (DEPTH_CONV bitstringLib.v2w_n2w_CONV) >> EVAL_TAC
QED
Theorem bootstrap_word_supported:
  i < 52 ==>
  supported_instruction (riscv$Decode
    (byte$word_of_bytes F (0w:word32) (TAKE 4 (DROP (4*i) bootstrapBytes))))
Proof
  mp_tac (PURE_REWRITE_RULE [bootstrapWords_def,EVERY_GENLIST]
    bootstrap_words_supported) >>
  simp [bootstrap_size]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "bootstrap instruction support assumptions")
  [words_literal,bootstrap_words_supported,bootstrap_word_supported];
