(* Composition and ROM preservation for the bootstrap execution trace. *)
Theory initBootstrapExecution
Ancestors initBootstrapPrefixSteps asmProps
Libs preamble wordsLib
open initBootstrapStepTheory asmSemTheory asmPropsTheory wordsTheory relationTheory
  initBootstrapLoopTheory initBootstrapIterationTheory initBootstrapMemoryTheory;
Theorem bootRun_append:
  !xs ys s. bootRun (xs ++ ys) s = bootRun ys (bootRun xs s)
Proof
  Induct >> simp [bootRun_def]
QED
Theorem bootSteps_append:
  !xs ys s. bootSteps (xs ++ ys) s <=>
    bootSteps xs s /\ bootSteps ys (bootRun xs s)
Proof
  Induct >> simp [bootSteps_def,bootRun_def] >> metis_tac []
QED
Theorem bootRun_consts:
  !xs s.
    (bootRun xs s).lr = s.lr /\ (bootRun xs s).align = s.align /\
    (bootRun xs s).be = s.be /\ (bootRun xs s).mem_domain = s.mem_domain
Proof
  Induct >> simp [bootRun_def,bootAfter_def,asm_consts]
QED
Theorem bootSteps_RTC:
  !xs s. bootSteps xs s ==>
    RTC (\s1 s2. ?instruction. asm_step riscv_config s1 instruction s2)
      s (bootRun xs s)
Proof
  Induct >> rw [bootSteps_def,bootRun_def] >>
  irule RTC_TRANS >> qexists_tac `bootAfter h s` >> conj_tac
  >- (irule RTC_SINGLE >> metis_tac []) >>
  first_x_assum irule >> fs []
QED
Theorem copy_iterations_consts:
  !n s.
    (copyIterations n s).lr = s.lr /\
    (copyIterations n s).align = s.align
Proof
  Induct >> simp [copyIterations_def,bootRun_consts]
QED
Theorem copy_loop_preserves_rom:
  bootstrapRomInvariant input s /\ ~s.be /\
  (!j. j < 8 ==> bootDataRam <= w2n (s.regs 6 + n2w j)) ==>
  bootstrapRomInvariant input (bootRun copyLoopBody s)
Proof
  rw [bootstrapRomInvariant_def,copy_loop_effect] >>
  `(copyWord s).mem a = s.mem a` by
    (irule copyWord_outside >> fs [] >> rpt strip_tac >>
     first_x_assum (qspec_then `j` mp_tac) >> fs [] >> decide_tac) >>
  metis_tac []
QED
Theorem copy_iterations_preserve_rom:
  bootstrapRomInvariant input s /\ ~s.be /\
  (!i j. i < n /\ j < 8 ==>
    bootDataRam <= w2n (s.regs 6 + n2w (8*i) + n2w j)) ==>
  bootstrapRomInvariant input (copyIterations n s)
Proof
  rw [bootstrapRomInvariant_def,copy_iterations_pointers] >>
  `(copyIterations n s).mem a = s.mem a` by
    (irule copy_iterations_outside >> fs [] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`i`,`j`] mp_tac) >> fs [] >> decide_tac) >>
  metis_tac []
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "bootstrap execution assumptions")
  [bootRun_append,bootSteps_append,bootRun_consts,bootSteps_RTC,
   copy_iterations_consts,copy_loop_preserves_rom,copy_iterations_preserve_rom];
