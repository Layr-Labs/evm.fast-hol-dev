(* Finite execution of all 4,616 bootstrap copy-loop iterations. *)
Theory initBootstrapChallengeCopyExecution
Ancestors initBootstrapChallengeCopySteps initBootstrapCopyExecution
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapLoopTheory
  initBootstrapIterationTheory initBootstrapExecutionTheory
  initBootstrapPrefixStepsTheory initBootstrapStepTheory;
open initBootstrapChallengeStepTheory initBootstrapCopyExecutionTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem copy_instructions_challenge_steps:
  !n s. (!i. i < n ==> challengeBootSteps copyLoopBody (copyIterations i s)) ==>
    challengeBootSteps (copyInstructions n) s
Proof
  Induct >> rw [copyInstructions_def,challengeBootSteps_def,challengeBootSteps_append,
    copy_instructions_run] >>
  metis_tac [LESS_TRANS,prim_recTheory.LESS_SUC_REFL]
QED
Theorem baseline_copy_iteration_challenge_steps:
  bootstrapRomInvariant input s /\ s.pc = 0x80000018w /\
  s.lr = 1 /\ ~s.be /\ s.align = 2 /\ ~s.failed /\
  s.regs 5 = n2w bootDataRom /\ s.regs 6 = n2w bootDataRam /\
  s.regs 7 = n2w bootDataEnd /\
  (!i. i < 36936 ==>
    n2w (bootDataRom+i) IN s.mem_domain /\
    n2w (bootDataRam+i) IN s.mem_domain) /\ n < 4617 ==>
  challengeBootSteps copyLoopBody (copyIterations n s)
Proof
  strip_tac >>
  `!k. k < 4617 ==>
    aligned 3 (s.regs 5 + n2w (8*k)) /\
    aligned 3 (s.regs 6 + n2w (8*k)) /\
    (!j. j < 8 ==> s.regs 5 + n2w (8*k) + n2w j IN s.mem_domain) /\
    (!j. j < 8 ==> s.regs 6 + n2w (8*k) + n2w j IN s.mem_domain) /\
    (!j. j < 8 ==> bootDataRam <= w2n (s.regs 6 + n2w (8*k) + n2w j))` by
    (match_mp_tac baseline_iteration_bounds >> asm_rewrite_tac []) >>
  `bootstrapRomInvariant input (copyIterations n s)` by
    (match_mp_tac copy_iterations_preserve_rom >> asm_rewrite_tac [] >>
     rpt strip_tac >> `i < 4617` by decide_tac >>
     qpat_x_assum `!k. k < 4617 ==> _` (qspec_then `i` mp_tac) >>
     asm_rewrite_tac [] >> metis_tac []) >>
  `~(copyIterations n s).failed` by
    (match_mp_tac copy_iterations_success >> asm_rewrite_tac [] >>
     rpt strip_tac >> `i < 4617` by decide_tac >>
     qpat_x_assum `!k. k < 4617 ==> _` (qspec_then `i` mp_tac) >>
     asm_rewrite_tac [] >> metis_tac []) >>
  `(copyIterations n s).pc = s.pc` by
    (irule copy_iterations_pc >>
     fs [bootDataRam_def,bootDataEnd_def,word_add_n2w,WORD_LO,dimword_64] >>
     rpt strip_tac >> decide_tac) >>
  irule copy_loop_challenge_steps >>
  fs [copy_iterations_consts,copy_iterations_pointers] >>
  qpat_x_assum `!k. k < 4617 ==> _` (qspec_then `n` mp_tac) >>
  asm_simp_tac std_ss [word_add_n2w,ADD_ASSOC,ADD_COMM] >> metis_tac []
QED
Theorem baseline_copy_challenge_execution:
  bootstrapRomInvariant input s /\ s.pc = 0x80000018w /\
  s.lr = 1 /\ ~s.be /\ s.align = 2 /\ ~s.failed /\
  s.regs 5 = n2w bootDataRom /\ s.regs 6 = n2w bootDataRam /\
  s.regs 7 = n2w bootDataEnd /\
  (!i. i < 36936 ==>
    n2w (bootDataRom+i) IN s.mem_domain /\
    n2w (bootDataRam+i) IN s.mem_domain) ==>
  RTC (initChallengeExecution$challengeAsmEdge (initSubmission$submissionConfig initBaselineAdmission$baselineSubmission))
    s (copyIterations 4617 s)
Proof
  strip_tac >> rewrite_tac [GSYM copy_instructions_run] >>
  irule challengeBootSteps_RTC >> irule copy_instructions_challenge_steps >>
  rpt strip_tac >> irule baseline_copy_iteration_challenge_steps >>
  fs [] >> metis_tac []
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "copy execution assumptions")
  [copy_instructions_run,copy_instructions_challenge_steps,baseline_iteration_bounds,
   baseline_copy_iteration_challenge_steps,baseline_copy_challenge_execution];
