(* Actual prefix instructions establish the copy-loop entry registers. *)
Theory initBootstrapStartup
Ancestors initBootstrapCopy
Libs preamble wordsLib cv_transLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapLoopTheory initParamsTheory;
Definition bootstrapPrefix_def:
  bootstrapPrefix = MAP SND (TAKE 3 bootstrapBlocks)
End
val prefix = save_thm ("bootstrap_prefix", EVAL ``bootstrapPrefix``);
val instructions = fst (listSyntax.dest_list (rhs (concl prefix)));
val enc_lengths = map (fn instr => cv_eval ``LENGTH (riscv_enc ^instr)``) instructions;
Theorem bootstrap_startup_effect:
  s.pc = n2w initialPc ==>
  (bootRun bootstrapPrefix s).regs 5 = n2w bootDataRom /\
  (bootRun bootstrapPrefix s).regs 6 = n2w bootDataRam /\
  (bootRun bootstrapPrefix s).regs 7 = n2w bootDataEnd /\
  (bootRun bootstrapPrefix s).pc = 0x80000018w /\
  (bootRun bootstrapPrefix s).mem = s.mem /\
  (bootRun bootstrapPrefix s).mem_domain = s.mem_domain /\
  (bootRun bootstrapPrefix s).be = s.be /\
  (bootRun bootstrapPrefix s).failed = s.failed /\
  (bootRun bootstrapPrefix s).align = s.align /\
  (bootRun bootstrapPrefix s).lr = s.lr
Proof
  strip_tac >>
  simp (enc_lengths @ [prefix,bootRun_def,bootAfter_def,asm_def,
    upd_pc_def,upd_reg_def,APPLY_UPDATE_THM,initialPc_def,
    bootDataRom_def,bootDataRam_def,bootDataEnd_def]) >> EVAL_TAC
QED
Definition bootCopyState_def:
  bootCopyState s = copyIterations 4617 (bootRun bootstrapPrefix s)
End
Theorem bootstrap_copy_effect:
  s.pc = n2w initialPc /\ ~s.be /\ ~s.failed /\
  (!i. i < 36936 ==>
    n2w (bootDataRom+i) IN s.mem_domain /\
    n2w (bootDataRam+i) IN s.mem_domain) ==>
  (bootCopyState s).pc = 0x8000002cw /\
  ~(bootCopyState s).failed /\
  (!i. i < 36936 ==>
    (bootCopyState s).mem (n2w (bootDataRam+i)) =
    s.mem (n2w (bootDataRom+i))) /\
  (!x. (!i. i < 36936 ==> x <> n2w (bootDataRam+i)) ==>
    (bootCopyState s).mem x = s.mem x)
Proof
  strip_tac >> imp_res_tac bootstrap_startup_effect >>
  simp [bootCopyState_def,baseline_copy_exit,baseline_copy_success,
    baseline_copy_all_bytes,baseline_copy_outside] >>
  conj_tac >- (irule baseline_copy_success >> fs []) >>
  mp_tac (Q.INST [`s` |-> `bootRun bootstrapPrefix s`] baseline_copy_all_bytes) >>
  fs []
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "startup assumptions")
  (bootstrap_startup_effect :: bootstrap_copy_effect :: enc_lengths);
