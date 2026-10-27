(* Iteration facts for the actual bootstrap copy-loop state update. *)
Theory initBootstrapIteration
Ancestors initBootstrapLoop
Libs preamble wordsLib
open asmSemTheory wordsTheory;
Definition copyIterations_def:
  copyIterations 0 s = s /\
  copyIterations (SUC n) s = copyIterations n (bootRun copyLoopBody s)
End
Theorem copy_iterations_pointers:
  !n s.
    (copyIterations n s).regs 5 = s.regs 5 + n2w (8*n) /\
    (copyIterations n s).regs 6 = s.regs 6 + n2w (8*n) /\
    (copyIterations n s).regs 7 = s.regs 7 /\
    (copyIterations n s).be = s.be /\
    (copyIterations n s).mem_domain = s.mem_domain
Proof
  Induct >> simp [copyIterations_def,copy_loop_effect,ADD1,
    LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC]
QED
Theorem copy_iterations_snoc:
  !n s. copyIterations (SUC n) s = bootRun copyLoopBody (copyIterations n s)
Proof
  Induct >- simp [copyIterations_def] >> fs [copyIterations_def]
QED
Theorem copy_iterations_outside:
  !n s x. ~s.be /\
    (!i j. i < n /\ j < 8 ==>
      x <> s.regs 6 + n2w (8*i) + n2w j) ==>
    (copyIterations n s).mem x = s.mem x
Proof
  Induct >- simp [copyIterations_def] >>
  rw [copy_iterations_snoc,copy_loop_effect] >>
  `~(copyIterations n s).be /\
    (!j. j < 8 ==> x <> (copyIterations n s).regs 6 + n2w j)` by
      (fs [copy_iterations_pointers] >> metis_tac [prim_recTheory.LESS_SUC_REFL]) >>
  `(copyWord (copyIterations n s)).mem x = (copyIterations n s).mem x` by
    (irule initBootstrapMemoryTheory.copyWord_outside >> simp []) >>
  asm_rewrite_tac [] >> first_x_assum irule >>
  fs [] >> metis_tac [LESS_TRANS,prim_recTheory.LESS_SUC_REFL]
QED
Theorem copy_iterations_success:
  !n s. ~s.be /\ ~s.failed /\
    (!i. i < n ==>
      aligned 3 (s.regs 5 + n2w (8*i)) /\
      aligned 3 (s.regs 6 + n2w (8*i)) /\
      (!j. j < 8 ==> s.regs 5 + n2w (8*i) + n2w j IN s.mem_domain) /\
      (!j. j < 8 ==> s.regs 6 + n2w (8*i) + n2w j IN s.mem_domain)) ==>
    ~(copyIterations n s).failed
Proof
  Induct >- simp [copyIterations_def] >>
  rw [copy_iterations_snoc,copy_loop_effect] >>
  irule initBootstrapMemoryTheory.copyWord_success >>
  simp [copy_iterations_pointers]
QED
Definition copySeparated_def:
  copySeparated n s =
    (!i k j l. i < n /\ k < n /\ j < 8 /\ l < 8 ==>
      s.regs 5 + n2w (8*i) + n2w j <> s.regs 6 + n2w (8*k) + n2w l /\
      (i <> k ==> s.regs 6 + n2w (8*i) + n2w j <>
                  s.regs 6 + n2w (8*k) + n2w l))
End
Theorem copy_separated_mono:
  copySeparated n s /\ m <= n ==> copySeparated m s
Proof
  rw [copySeparated_def] >> metis_tac [LESS_LESS_EQ_TRANS]
QED
Theorem copy_iterations_bytes:
  !n s. ~s.be /\ copySeparated n s ==>
    !k j. k < n /\ j < 8 ==>
      (copyIterations n s).mem (s.regs 6 + n2w (8*k) + n2w j) =
      s.mem (s.regs 5 + n2w (8*k) + n2w j)
Proof
  Induct >- simp [] >> rpt strip_tac >>
  `copySeparated n s` by metis_tac [copy_separated_mono,LESS_EQ_SUC_REFL] >>
  Cases_on `k = n`
  >- (fs [copy_iterations_snoc,copy_loop_effect] >>
      `~(copyIterations n s).be` by simp [copy_iterations_pointers] >>
      mp_tac (Q.INST [`s` |-> `copyIterations n s`] initBootstrapMemoryTheory.copyWord_bytes) >>
      simp [copy_iterations_pointers] >> disch_then (qspec_then `j` mp_tac) >>
      simp [] >> disch_then kall_tac >>
      irule copy_iterations_outside >>
      fs [copySeparated_def] >> metis_tac [LESS_TRANS,prim_recTheory.LESS_SUC_REFL]) >>
  `k < n` by decide_tac >>
  rw [copy_iterations_snoc,copy_loop_effect] >>
  `(copyWord (copyIterations n s)).mem (s.regs 6 + n2w (8*k) + n2w j) =
    (copyIterations n s).mem (s.regs 6 + n2w (8*k) + n2w j)` by
    (irule initBootstrapMemoryTheory.copyWord_outside >>
     simp [copy_iterations_pointers] >> fs [copySeparated_def] >>
     metis_tac [LESS_TRANS,prim_recTheory.LESS_SUC_REFL]) >>
  fs []
QED
Theorem copy_iterations_pc:
  !n s. (!i. i < n ==> s.regs 6 + n2w (8 * SUC i) <+ s.regs 7) ==>
    (copyIterations n s).pc = s.pc
Proof
  Induct >- simp [copyIterations_def] >>
  rw [copy_iterations_snoc,copy_loop_effect,copy_iterations_pointers] >>
  fs [ADD1,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC] >>
  metis_tac [DECIDE ``(n:num) < n + 1``, DECIDE ``(i:num) < n ==> i < n+1``]
QED
Theorem copy_iterations_exit:
  (!i. i < n ==> s.regs 6 + n2w (8 * SUC i) <+ s.regs 7) /\
  ~(s.regs 6 + n2w (8 * SUC n) <+ s.regs 7) ==>
  (copyIterations (SUC n) s).pc = s.pc + 20w
Proof
  strip_tac >>
  `(copyIterations n s).pc = s.pc` by metis_tac [copy_iterations_pc] >>
  fs [copy_iterations_snoc,copy_loop_effect,copy_iterations_pointers,
      ADD1,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "copy iteration assumptions")
  [copy_iterations_pointers,copy_iterations_snoc,copy_iterations_outside,copy_iterations_success,copy_separated_mono,copy_iterations_bytes,copy_iterations_pc,copy_iterations_exit];
