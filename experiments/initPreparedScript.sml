(* The top-level Pancake compiler moves main before compiling its declarations.
   Keep the authoritative source AST unchanged and evaluate this compiler step. *)
Theory initPrepared
Ancestors initCrep pan_to_target
Libs preamble cv_transLib
(* Do not pretty-print giant evaluated program literals into HTML. *)
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name, check_thm th)
  else failwith "prepared compiler result has assumptions";
Definition mainFirst_def:
  mainFirst (prog : 64 panLang$decl list) =
    case SPLITP (\x. case x of Function fi => fi.name = «main» | _ => F) prog of
      ([],ys) => ys
    | (xs,[]) => Function (fun_decl «main» F F [] (Return (Const 0w)) One)::xs
    | (xs,y::ys) => y::xs ++ ys
End
(* SPLITP's specification duplicates its recursive call. Use HOL's proved
   tail-recursive equation so a late main declaration does not take exponential time. *)
Theorem splitp_tailrec[cv_inline] = rich_listTheory.SPLITP_compute;
val _ = cv_auto_trans mainFirst_def;
Definition prepared_guest_def:
  prepared_guest = guestFn_main :: TAKE (LENGTH guestAst - 1) guestAst
End
val _ = cv_auto_trans prepared_guest_def;
val _ = save_closed "guest_main_first"
  (EQT_ELIM (cv_eval ``mainFirst guestAst = prepared_guest``));
val _ = save_closed "prepared_simplified"
  (cv_eval_pat (cvName "prepared_simple") ``pan_simp$compile_prog prepared_guest``);
val _ = save_closed "prepared_structures"
  (cv_eval_pat (cvName "prepared_structs") ``pan_structs$compile_top prepared_simple``);
val _ = save_closed "prepared_global_declarations"
  (cv_eval_pat (cvName "prepared_globals") ``pan_globals$compile_top prepared_structs «main»``);
val no_inline = cv_eval ``inlineNames prepared_globals = []``;
val no_inline = EQT_ELIM no_inline |> REWRITE_RULE [inlineNames_def];
val declarations = cv_eval_pat (cvName "prepared_crep")
  ``pan_to_crep$compile_to_crep prepared_globals``;
val _ = save_closed "prepared_crep_declarations" declarations;
val _ = save_closed "prepared_crep_compilation"
  (TRANS (MATCH_MP crepNoInlineTheory.no_inline_compile no_inline) declarations);
