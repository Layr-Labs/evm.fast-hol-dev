Theory initGlobals
Ancestors initStructs panGlobalsCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val result = cv_eval_pat (cvName "globals_guest")
  ``pan_globals$compile_top structured_guest «main»``;
val _ = if null (hyp result) then
  save_thm ("guest_globals", check_thm result)
  else failwith "globals compilation has assumptions";
