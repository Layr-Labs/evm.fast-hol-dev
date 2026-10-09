(* Compose startup, the finite copy loop, and initialization through native entry. *)
Theory initBootstrapFullExecution
Ancestors initBootstrapSuffixSteps
Libs preamble wordsLib
open asmSemTheory wordsTheory relationTheory initBootstrapTheory initParamsTheory
  initBootstrapStepTheory initBootstrapExecutionTheory initBootstrapLoopTheory
  initBootstrapStartupTheory initBootstrapIterationTheory initBootstrapFrameTheory
  initBootstrapStateTheory initBootstrapPrefixStepsTheory initBootstrapCopyExecutionTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem bootstrap_startup_rom:
  bootstrapRomInvariant input s /\ s.pc = n2w initialPc ==>
  bootstrapRomInvariant input (bootRun bootstrapPrefix s)
Proof
  strip_tac >> imp_res_tac bootstrap_startup_effect >>
  fs [bootstrapRomInvariant_def]
QED
Theorem bootstrap_copy_rom:
  bootstrapRomInvariant input s /\ s.pc = n2w initialPc /\ ~s.be ==>
  bootstrapRomInvariant input (bootCopyState s)
Proof
  strip_tac >> imp_res_tac bootstrap_copy_entry >>
  rw [bootstrapRomInvariant_def] >>
  TRY (fs [bootstrapRomInvariant_def] >> NO_TAC) >>
  `(bootCopyState s).mem a = s.mem a` by
    (irule copy_preserves_low_memory >> fs []) >>
  fs [bootstrapRomInvariant_def] >> metis_tac []
QED
Theorem bootstrap_full_execution:
  bootstrapRomInvariant input s /\ s.pc = n2w initialPc /\
  s.lr = 1 /\ ~s.be /\ s.align = 2 /\ ~s.failed /\
  (!i. i < 36936 ==>
    n2w (bootDataRom+i) IN s.mem_domain /\
    n2w (bootDataRam+i) IN s.mem_domain) /\
  (!i. i < 40 ==> n2w (0xa1000000+i) IN s.mem_domain) ==>
  RTC (\s1 s2. ?instruction. asm_step riscv_config s1 instruction s2)
    s (bootFinalState s)
Proof
  strip_tac >>
  `bootstrapRomInvariant input (bootRun bootstrapPrefix s)` by
    metis_tac [bootstrap_startup_rom] >>
  `bootstrapRomInvariant input (bootCopyState s)` by
    metis_tac [bootstrap_copy_rom] >>
  imp_res_tac bootstrap_startup_effect >>
  imp_res_tac bootstrap_copy_entry >> imp_res_tac bootstrap_copy_effect >>
  irule RTC_TRANS >> qexists_tac `bootRun bootstrapPrefix s` >> conj_tac
  >- (irule bootSteps_RTC >> irule bootstrap_prefix_steps >> fs [] >> metis_tac []) >>
  irule RTC_TRANS >> qexists_tac `bootCopyState s` >> conj_tac
  >- (rewrite_tac [bootCopyState_def] >> irule baseline_copy_execution >>
      fs [] >> metis_tac []) >>
  rewrite_tac [bootFinalState_def] >>
  irule bootSteps_RTC >> irule bootstrap_suffix_steps >>
  fs [bootCopyState_def,copy_iterations_consts,bootRun_consts] >>
  metis_tac [DECIDE ``(i:num) < 24 ==> i < 36936``,bootDataRam_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "full bootstrap execution assumptions")
  [bootstrap_startup_rom,bootstrap_copy_rom,bootstrap_full_execution];
