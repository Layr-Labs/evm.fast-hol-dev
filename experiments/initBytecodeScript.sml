(* Native register allocation is an untrusted hint: from_word_0_riscv
   checks the complete colouring in HOL before it can return any bytes. *)
Theory initBytecode
Ancestors initCompilationInput pancakeBackendBridge
Libs preamble cv_transLib reg_allocComputeLib
(* Avoid pretty-printing giant evaluated literals into HTML documentation. *)
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name, check_thm th)
  else failwith (name ^ " has assumptions");
fun report s = print ("initBytecode: " ^ s ^ "\n");
val _ = report "computing register-allocation graphs";
val graphs = cv_eval_raw
  ``FST (riscvBackendDefs$to_livesets_0_riscv
        (guestConfig,prepared_word,guestNames))``;
val _ = check_thm graphs;
val _ = report "generating an untrusted allocation hint";
val colours = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc (rconc graphs);
val allocation_def = new_definition ("allocation_def",
  mk_eq (mk_var ("allocation",type_of colours),colours));
val _ = cv_trans_deep_embedding EVAL allocation_def;
val _ = cv_auto_trans backendTheory.set_oracle_def;
val _ = report "checking the allocation and compiling RISC-V bytes";
val result = cv_eval_pat (cvName "backend_output")
  ``riscvBackendDefs$from_word_0_riscv
    (set_oracle guestConfig allocation, prepared_word, guestNames)``;
val _ = save_closed "checked_backend_output" result;
val _ = save_closed "backend_succeeded"
  (EQT_ELIM (cv_eval ``IS_SOME backend_output``));
Definition compiledBytes_def:
  compiledBytes = case backend_output of
    NONE => [] | SOME (bytes,blen,bm,bmlen,ffi,shmem,syms,conf) => bytes
End
val _ = cv_auto_trans compiledBytes_def;
val _ = save_closed "compiled_byte_count" (cv_eval ``LENGTH compiledBytes``);
val _ = report "exporting raw compiler byte array";
val bytes_thm = cv_eval_raw ``compiledBytes``;
val _ = check_thm bytes_thm;
val bytes_cv = rand (rconc bytes_thm);
val stream = BinIO.openOut "compiled.bin";
fun write_bytes tm =
  if cvSyntax.is_cv_pair tm then
    let val (n,rest) = cvSyntax.dest_cv_pair tm
        val byte = numSyntax.int_of_term (cvSyntax.dest_cv_num n)
        val _ = if 0 <= byte andalso byte < 256 then () else failwith "invalid byte"
    in BinIO.output1 (stream,Word8.fromInt byte); write_bytes rest end
  else if aconv tm (cvSyntax.mk_cv_num numSyntax.zero_tm) then ()
  else failwith "invalid byte-list terminator";
val _ = (write_bytes bytes_cv; BinIO.closeOut stream);
