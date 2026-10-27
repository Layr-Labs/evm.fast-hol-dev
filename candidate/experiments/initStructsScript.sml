Theory initStructs
Ancestors initSimplify panStructsTopCv
Libs preamble cv_transLib
val _ = cv_memLib.use_long_names := true;
val result = cv_eval_pat (cvName "structured_guest")
  ``pan_structs$compile_top simplified_guest``;
val _ = if null (hyp result) then
  save_thm ("guest_structures", check_thm result)
  else failwith "structure compilation has assumptions";
