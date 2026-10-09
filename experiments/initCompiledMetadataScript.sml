Theory initCompiledMetadata
Ancestors initDecodedConfig
Libs preamble cv_transLib
open initArtifactsTheory initDecodedConfigTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name,check_thm th)
  else failwith (name ^ " has assumptions");
Definition compiledFfiNames_def:
  compiledFfiNames = THE compiledConfig.lab_conf.ffi_names
End
val _ = cv_trans (CONV_RULE (RAND_CONV (REWRITE_CONV [decoded_config, candidateConfig_def] THENC EVAL)) compiledFfiNames_def);
Definition compiledMmio_def:
  compiledMmio = compiledConfig.lab_conf.shmem_extra
End
val _ = cv_trans (CONV_RULE (RAND_CONV (REWRITE_CONV [decoded_config, candidateConfig_def] THENC EVAL)) compiledMmio_def);
Definition compiledFirst_def:
  compiledFirst = LENGTH (FILTER
    (\nm. case nm of ExtCall _ => T | SharedMem _ => F) compiledFfiNames)
End
val _ = cv_auto_trans compiledFirst_def;
val _ = save_closed "compiled_ffi_count" (cv_eval ``LENGTH compiledFfiNames``);
val _ = save_closed "compiled_mmio_count" (cv_eval ``LENGTH compiledMmio``);
val _ = save_closed "compiled_first" (cv_eval ``compiledFirst``);
Definition compiledOffsetsNonnegative_def:
  compiledOffsetsNonnegative = EVERY
    (\rec : lab_to_target$shmem_info_num. 0 <= rec.addr_off) compiledMmio
End
val _ = cv_auto_trans compiledOffsetsNonnegative_def;
val _ = save_closed "compiled_offsets_nonnegative"
  (EQT_ELIM (cv_eval ``compiledOffsetsNonnegative``));
