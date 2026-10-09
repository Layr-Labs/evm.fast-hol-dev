(* Compose all bootstrap assembler state updates, through native entry. *)
Theory initBootstrapState
Ancestors initBootstrapSuffix
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapTheory initParamsTheory
  initBootstrapStartupTheory initBootstrapIterationTheory;
Definition bootFinalState_def:
  bootFinalState s = bootRun bootstrapSuffix (bootCopyState s)
End
Theorem bootstrap_final_effect:
  s.pc = n2w initialPc /\ ~s.be /\ ~s.failed /\
  (!i. i < 36936 ==>
    n2w (bootDataRom+i) IN s.mem_domain /\
    n2w (bootDataRam+i) IN s.mem_domain) /\
  (!i. i < 40 ==> n2w (0xa1000000+i) IN s.mem_domain) ==>
  (bootFinalState s).pc = n2w baselineNativePc /\
  (bootFinalState s).regs 10 = n2w baselineNativePc /\
  (bootFinalState s).regs 11 = 0xa1000000w /\
  (bootFinalState s).regs 12 = 0x7df000000w /\
  (bootFinalState s).regs 13 = 0x7e0000000w /\
  ~(bootFinalState s).failed /\
  (bootFinalState s).mem = bootstrapStoredBytes (bootCopyState s).mem
Proof
  strip_tac >> imp_res_tac bootstrap_copy_effect >>
  `(bootCopyState s).be = s.be /\
   (bootCopyState s).mem_domain = s.mem_domain` by
    (simp [bootCopyState_def,copy_iterations_pointers] >>
     imp_res_tac bootstrap_startup_effect >> fs []) >>
  imp_res_tac bootstrap_suffix_registers >>
  simp [bootFinalState_def,bootstrap_suffix_memory] >>
  irule bootstrap_suffix_success >>
  fs [bootDataRam_def] >>
  metis_tac [DECIDE ``(i:num) < 24 ==> i < 36936``]
QED
val _ = if null (hyp bootstrap_final_effect)
  then ignore (check_thm bootstrap_final_effect)
  else failwith "bootstrap final effect assumptions";
