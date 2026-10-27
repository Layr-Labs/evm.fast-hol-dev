(* Exact compiler metadata used by the native installation contract. *)
Theory initInstallationMetadata
Ancestors initDecodedConfig initCompiledMetadata
Libs preamble cv_transLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th = if null(hyp th) then save_thm(name,check_thm th)
  else failwith (name ^ " has assumptions");
val _ = save_closed "compiled_installation_names"
  (EQT_ELIM (cv_eval ``compiledConfig.lab_conf.ffi_names = SOME compiledFfiNames``));
val _ = save_closed "compiled_installation_mmio"
  (EQT_ELIM (cv_eval ``compiledConfig.lab_conf.shmem_extra = compiledMmio``));
