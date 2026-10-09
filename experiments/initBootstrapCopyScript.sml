(* Specialise the finite copy proof to the fixed baseline ROM/RAM layout. *)
Theory initBootstrapCopy
Ancestors initBootstrapIteration
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapTheory;
Theorem baseline_copy_separated:
  (s:64 asm_state).regs 5 = n2w bootDataRom /\
  s.regs 6 = n2w bootDataRam ==>
  copySeparated 4617 s
Proof
  rw [copySeparated_def,bootDataRom_def,bootDataRam_def] >>
  simp [word_add_n2w,n2w_11,dimword_64] >> decide_tac
QED
Theorem baseline_copy_exit:
  s.regs 6 = n2w bootDataRam /\ s.regs 7 = n2w bootDataEnd ==>
  (copyIterations 4617 s).pc = s.pc + 20w
Proof
  strip_tac >> once_rewrite_tac [DECIDE ``4617 = SUC 4616``] >>
  irule copy_iterations_exit >>
  fs [bootDataRam_def,bootDataEnd_def,word_add_n2w,WORD_LO,dimword_64] >>
  rpt strip_tac >> decide_tac
QED
Theorem baseline_copy_bytes:
  ~s.be /\ s.regs 5 = n2w bootDataRom /\ s.regs 6 = n2w bootDataRam ==>
  !k j. k < 4617 /\ j < 8 ==>
    (copyIterations 4617 s).mem (n2w (bootDataRam + 8*k + j)) =
    s.mem (n2w (bootDataRom + 8*k + j))
Proof
  strip_tac >>
  `copySeparated 4617 s` by metis_tac [baseline_copy_separated] >>
  mp_tac (Q.SPECL [`4617`,`s`] copy_iterations_bytes) >>
  fs [word_add_n2w]
QED
Theorem baseline_copy_success:
  ~s.be /\ ~s.failed /\
  s.regs 5 = n2w bootDataRom /\ s.regs 6 = n2w bootDataRam /\
  (!i. i < 36936 ==>
    n2w (bootDataRom + i) IN s.mem_domain /\
    n2w (bootDataRam + i) IN s.mem_domain) ==>
  ~(copyIterations 4617 s).failed
Proof
  strip_tac >> irule copy_iterations_success >>
  fs [word_add_n2w,bootDataRom_def,bootDataRam_def] >>
  rpt strip_tac >>
  fs [aligned_w2n,word_add_n2w,w2n_n2w,dimword_64] >>
  TRY decide_tac >> `8*i+j < 36936` by decide_tac >>
  first_x_assum (qspec_then `8*i+j` mp_tac) >> asm_simp_tac std_ss [ADD_ASSOC]
QED
Theorem baseline_copy_all_bytes:
  ~s.be /\ s.regs 5 = n2w bootDataRom /\ s.regs 6 = n2w bootDataRam ==>
  !i. i < 36936 ==>
    (copyIterations 4617 s).mem (n2w (bootDataRam + i)) =
    s.mem (n2w (bootDataRom + i))
Proof
  rpt strip_tac >>
  `i DIV 8 < 4617 /\ i MOD 8 < 8 /\ 8 * (i DIV 8) + i MOD 8 = i` by
    (simp [DIV_LT_X] >> metis_tac [DIVISION,DECIDE ``0 < 8:num``,MULT_COMM]) >>
  mp_tac (Q.INST [`s` |-> `s`] baseline_copy_bytes) >>
  asm_simp_tac std_ss [] >>
  disch_then (qspecl_then [`i DIV 8`,`i MOD 8`] mp_tac) >>
  asm_simp_tac std_ss [GSYM ADD_ASSOC]
QED
Theorem baseline_copy_outside:
  ~s.be /\ s.regs 6 = n2w bootDataRam /\
  (!i. i < 36936 ==> x <> n2w (bootDataRam+i)) ==>
  (copyIterations 4617 s).mem x = s.mem x
Proof
  strip_tac >> irule copy_iterations_outside >>
  fs [word_add_n2w] >> rpt strip_tac >>
  `8*i+j < 36936` by decide_tac >>
  first_x_assum (qspec_then `8*i+j` mp_tac) >>
  asm_simp_tac std_ss [ADD_ASSOC]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "baseline copy assumptions")
  [baseline_copy_separated,baseline_copy_exit,baseline_copy_bytes,
   baseline_copy_success,baseline_copy_all_bytes,baseline_copy_outside];
