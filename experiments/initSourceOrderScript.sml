(* Connect compiler declaration order to the fixed challenge source. *)
Theory initSourceOrder
Ancestors initSourceChecks initSource panMainOrder
Libs preamble cv_transLib
open initPreparedTheory initGuestTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name,check_thm th)
  else failwith (name ^ " has assumptions");
Definition guestPrefix_def:
  guestPrefix = TAKE (LENGTH guestAst - 1) guestAst
End
val _ = cv_auto_trans guestPrefix_def;
val guest_split = save_closed "guest_split"
  (EQT_ELIM (cv_eval ``guestAst = guestPrefix ++ [guestFn_main]``));
Definition prefixHasNoMain_def:
  prefixHasNoMain = ~MEM «main» (MAP FST (functions guestPrefix))
End
val _ = cv_auto_trans prefixHasNoMain_def;
val prefix_no_main = save_closed "prefix_no_main"
  (REWRITE_RULE [prefixHasNoMain_def]
    (EQT_ELIM (cv_eval ``prefixHasNoMain``)));
Definition guestMainIsMain_def:
  guestMainIsMain =
    case guestFn_main of Function fi => fi.name = «main» | _ => F
End
val _ = cv_auto_trans guestMainIsMain_def;
val main_name = save_closed "main_name"
  (EQT_ELIM (cv_eval ``guestMainIsMain``));
Theorem main_function_exists:
  ?fi. guestFn_main = Function fi /\ fi.name = «main»
Proof
  mp_tac main_name >> Cases_on `guestFn_main` >> fs [guestMainIsMain_def]
QED
Theorem prepared_prefix:
  prepared_guest = guestFn_main :: guestPrefix
Proof
  simp [prepared_guest_def,guestPrefix_def]
QED
Theorem prepared_source_semantics:
  semantics_decls (s : (64,'ffi) panSem$state) start prepared_guest =
  semantics_decls s start guestAst
Proof
  strip_assume_tac main_function_exists >>
  rewrite_tac [prepared_prefix,guest_split] >>
  asm_simp_tac std_ss [] >>
  irule semantics_function_move >> fs [prefix_no_main]
QED
Theorem prepared_fixed_source_behaviour:
  semantics_decls (sourceInitialState input) «main» prepared_guest =
  sourceBehaviour input
Proof
  simp [prepared_source_semantics,sourceBehaviour_def,sourceBehaviourFor_def,
    sourceInitialState_def]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore(check_thm th) else failwith "source order assumptions")
  [main_function_exists,prepared_prefix,prepared_source_semantics,
   prepared_fixed_source_behaviour];
