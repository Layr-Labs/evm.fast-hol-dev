(* First full-guest compiler-pass experiment, using kernel checked cv evaluation. *)
Theory initSimplify
Ancestors initGuest panSimplifyCv
Libs preamble cv_transLib

val _ = cv_memLib.use_long_names := true;

(* Register literal definitions in their source order, without generating a
   separate proof script for every guest function. *)
Theorem literal_fun_decl:
  (<|name := n; inline := i; export := e; params := ps;
     body := b; return := r|> : 64 panLang$fun_decl) =
  fun_decl n i e ps b r
Proof
  simp [panLangTheory.fun_decl_component_equality]
QED

val literal_conv =
  REWRITE_CONV [literal_fun_decl] THENC EVAL THENC
  REWRITE_CONV [cvTheory.b2c_def];
val declarations = fst (listSyntax.dest_list (rhs (concl guestAst_def)));
val _ = List.app
  (fn tm => cv_trans_deep_embedding literal_conv (DB.fetch "initGuest" (#Name (dest_thy_const tm) ^ "_def")))
  declarations;
val _ = cv_trans guestAst_def;

fun save_closed (name, th) =
  if null (hyp th) then save_thm (name, check_thm th)
  else failwith (name ^ " has undischarged assumptions");

val _ = save_closed ("guest_declaration_count", cv_eval ``LENGTH guestAst``);
val _ = save_closed ("guest_simplified",
  cv_eval_pat (cvName "simplified_guest")
    ``pan_simp$compile_prog guestAst``);
