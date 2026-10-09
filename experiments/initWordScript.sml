Theory initWord
Ancestors initLoops panWordCv
Libs preamble cv_transLib
(* Do not pretty-print giant evaluated program literals into HTML. *)
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
val result = cv_eval_pat (cvName "prepared_word")
  ``loop_to_word$compile prepared_loop``;
val _ = if null (hyp result) then save_thm ("prepared_word_compilation", check_thm result)
  else failwith "word compilation has assumptions";
