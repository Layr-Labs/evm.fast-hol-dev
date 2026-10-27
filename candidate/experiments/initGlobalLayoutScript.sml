(* Evaluate the global layout used by the fixed source and compiler theorem. *)
Theory initGlobalLayout
Ancestors initSourceChecks initSource
Libs preamble cv_transLib wordsLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name, check_thm th)
  else failwith (name ^ " has assumptions");
Definition guestStructContext_def:
  guestStructContext = panSem$decs_stcnames [] prepared_guest
End
Definition guestNoNames_def:
  guestNoNames = EVERY (\d. is_function d \/ is_decl d \/ is_exn_decl d)
    prepared_guest
End
val _ = cv_auto_trans guestNoNames_def;
val prepared_no_names = save_closed "prepared_no_names"
  (REWRITE_RULE [guestNoNames_def] (EQT_ELIM (cv_eval ``guestNoNames``)));
Theorem prepared_struct_context:
  panSem$decs_stcnames [] prepared_guest = SOME []
Proof
  irule panPropsTheory.decs_stcnames_only_functions >>
  ACCEPT_TAC prepared_no_names
QED
val _ = cv_auto_trans
  (INST_TYPE [alpha |-> ``:64``] pan_globalsTheory.dec_shapes_def);
val prepared_global_shapes = save_closed "prepared_global_shapes"
  (cv_eval ``pan_globals$dec_shapes prepared_guest``);
Definition guestGlobalsSize_def:
  guestGlobalsSize = SUM (MAP
    (size_of_sh_with_ctxt (THE guestStructContext))
    (pan_globals$dec_shapes prepared_guest))
End
val prepared_globals_size = save_closed "prepared_globals_size"
  ((REWRITE_CONV [guestGlobalsSize_def,guestStructContext_def,
      prepared_struct_context,prepared_global_shapes] THENC EVAL)
    ``guestGlobalsSize``);
Theorem prepared_globals_match_source:
  SUM (MAP (size_of_sh_with_ctxt
    (THE (panSem$decs_stcnames [] prepared_guest)))
    (pan_globals$dec_shapes prepared_guest)) = globalsWords
Proof
  rewrite_tac [GSYM guestStructContext_def,GSYM guestGlobalsSize_def] >>
  simp [prepared_globals_size,initParamsTheory.globalsWords_def]
QED
