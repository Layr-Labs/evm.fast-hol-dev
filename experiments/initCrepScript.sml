Theory initCrep
Ancestors initGlobals panCrepCv crepNoInline
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name, check_thm th)
  else failwith "crep compilation has assumptions";
Definition inlineNames_def:
  inlineNames (ps : 64 panLang$decl list) =
    MAP FST (panLang$functions (FILTER panLang$inlinable ps))
End
val _ = cv_auto_trans inlineNames_def;
val no_inline = cv_eval ``inlineNames globals_guest = []``;
val guest_has_no_inline_functions = save_closed "guest_has_no_inline_functions"
  (EQT_ELIM no_inline |> REWRITE_RULE [inlineNames_def]);
val result = cv_eval_pat (cvName "crep_guest")
  ``pan_to_crep$compile_to_crep globals_guest``;
val guest_crep_declarations = save_closed "guest_crep_declarations" result;
Theorem guest_crep:
  pan_to_crep$compile_prog globals_guest = crep_guest
Proof
  irule EQ_TRANS >> qexists_tac `pan_to_crep$compile_to_crep globals_guest` >>
  conj_tac >- (irule no_inline_compile >> ACCEPT_TAC guest_has_no_inline_functions) >>
  ACCEPT_TAC guest_crep_declarations
QED
