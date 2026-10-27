(* Compiler artifacts only: these are not yet a bootstrapped challenge ROM. *)
Theory initArtifacts
Ancestors initCompileProof
Libs preamble cv_transLib
(* Avoid pretty-printing giant evaluated literals into HTML documentation. *)
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th = if null (hyp th) then save_thm (name,check_thm th)
  else failwith (name ^ " has assumptions");
Definition compiledBitmaps_def:
  compiledBitmaps = case backend_output of
    NONE => [] | SOME (bytes,blen,bm,bmlen,ffi,shmem,syms,conf) => bm
End
Definition compiledBackendConfig_def:
  compiledBackendConfig = case backend_output of
    NONE => [] | SOME (bytes,blen,bm,bmlen,ffi,shmem,syms,conf) => conf
End
Definition compiledConfig_def:
  compiledConfig = backend_enc_dec$decode_backend_config compiledBackendConfig
End
Theorem exact_guest_riscv_compilation:
  pan_to_target$compile_prog riscv_config
    (set_oracle pancakeRiscvConfig allocation) guestAst =
    SOME (compiledBytes,compiledBitmaps,compiledConfig)
Proof
  `?out. backend_output = SOME out` by
    metis_tac [initBytecodeTheory.backend_succeeded,optionTheory.IS_SOME_EXISTS] >>
  PairCases_on `out` >>
  mp_tac (initBytecodeTheory.checked_backend_output |>
    REWRITE_RULE [GSYM riscvBackendDefsTheory.from_word_0_riscv_eq]) >>
  asm_rewrite_tac [] >>
  disch_then (strip_assume_tac o MATCH_MP pancakeBackendBridgeTheory.from_word_0_thm) >>
  fs [initCompilationInputTheory.top_compile_to_backend,
      initBytecodeTheory.compiledBytes_def,compiledBitmaps_def,
      compiledConfig_def,compiledBackendConfig_def,
      backend_enc_decTheory.encode_backend_config_thm]
QED
val _ = save_closed "checked_exact_compilation" exact_guest_riscv_compilation;
val _ = cv_auto_trans compiledBitmaps_def;
val _ = cv_auto_trans compiledBackendConfig_def;
val _ = save_closed "compiled_bitmap_count" (cv_eval ``LENGTH compiledBitmaps``);
fun raw_list term =
  let val th = cv_eval_raw term
      val _ = check_thm th
  in rand (rconc th) end;
fun each_cv f tm =
  if cvSyntax.is_cv_pair tm then
    let val (n,rest) = cvSyntax.dest_cv_pair tm
    in f (numSyntax.dest_numeral (cvSyntax.dest_cv_num n)); each_cv f rest end
  else if aconv tm (cvSyntax.mk_cv_num numSyntax.zero_tm) then ()
  else failwith "invalid artifact list terminator";
val bitmap_stream = TextIO.openOut "bitmaps.txt";
val _ = each_cv (fn n => TextIO.output (bitmap_stream,Arbnum.toString n ^ "\n"))
  (raw_list ``compiledBitmaps``);
val _ = TextIO.closeOut bitmap_stream;
val config_stream = BinIO.openOut "backend.conf";
val _ = each_cv (fn n =>
  let val b = Arbnum.toInt n
  in if 0 <= b andalso b < 256 then BinIO.output1 (config_stream,Word8.fromInt b)
     else failwith "invalid configuration byte" end)
  (raw_list ``compiledBackendConfig``);
val _ = BinIO.closeOut config_stream;
