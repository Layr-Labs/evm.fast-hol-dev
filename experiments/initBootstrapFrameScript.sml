(* Preservation of executable ROM and copied bitmap bytes. *)
Theory initBootstrapFrame
Ancestors initBootstrapState
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapStoresTheory initBootstrapSuffixTheory
  initBootstrapTheory initBootstrapStartupTheory initBootstrapIterationTheory
  initBootstrapCopyTheory;
Theorem little_store_below:
  w2n x < a /\ a + 8 < 2**64 ==>
  littleStore 8 (n2w a) w bytesAt x = bytesAt x
Proof
  strip_tac >> irule little_store_outside >>
  rw [word_add_n2w] >> strip_tac >> fs [w2n_n2w,dimword_64] >> decide_tac
QED
Theorem suffix_preserves_low_memory:
  w2n x < 0xa0020000 ==>
  bootstrapStoredBytes bytesAt x = bytesAt x
Proof
  strip_tac >>
  `!a w bytesAt. 0xa0020000 <= a /\ a + 8 < 2**64 ==>
     littleStore 8 (n2w a) w bytesAt x = bytesAt x` by
    (rpt strip_tac >> irule little_store_below >>
     metis_tac [LESS_LESS_EQ_TRANS]) >>
  simp [bootstrapStoredBytes_def]
QED
Theorem copy_preserves_low_memory:
  ~s.be /\ s.pc = n2w initParams$initialPc /\ w2n x < bootDataRam ==>
  (bootCopyState s).mem x = s.mem x
Proof
  strip_tac >> simp [bootCopyState_def] >>
  imp_res_tac bootstrap_startup_effect >>
  `(copyIterations 4617 (bootRun bootstrapPrefix s)).mem x =
   (bootRun bootstrapPrefix s).mem x` by
    (irule baseline_copy_outside >> fs [] >>
     rw [bootDataRam_def] >> strip_tac >>
     fs [bootDataRam_def,w2n_n2w,dimword_64] >> decide_tac) >>
  fs []
QED
Theorem bootstrap_copy_entry:
  s.pc = n2w initParams$initialPc ==>
  (bootCopyState s).pc = 0x8000002cw /\
  (bootCopyState s).be = s.be /\
  (bootCopyState s).mem_domain = s.mem_domain
Proof
  strip_tac >> imp_res_tac bootstrap_startup_effect >>
  simp [bootCopyState_def,copy_iterations_pointers,baseline_copy_exit]
QED
Theorem bootstrap_preserves_low_memory:
  ~s.be /\ s.pc = n2w initParams$initialPc /\ w2n x < bootDataRam ==>
  (bootFinalState s).mem x = s.mem x
Proof
  strip_tac >> imp_res_tac bootstrap_copy_entry >>
  simp [bootFinalState_def,bootstrap_suffix_memory] >>
  `w2n x < 0xa0020000` by fs [bootDataRam_def] >>
  simp [suffix_preserves_low_memory] >>
  irule copy_preserves_low_memory >> fs []
QED
Theorem bootstrap_preserves_domain:
  s.pc = n2w initParams$initialPc ==>
  (bootFinalState s).mem_domain = s.mem_domain /\
  (bootFinalState s).be = s.be
Proof
  strip_tac >> imp_res_tac bootstrap_copy_entry >>
  imp_res_tac bootstrap_suffix_registers >> simp [bootFinalState_def]
QED
Theorem bootstrap_preserves_bytes:
  ~s.be /\ s.pc = n2w initParams$initialPc /\
  a + LENGTH bytes <= bootDataRam /\
  bytes_in_memory (n2w a) bytes s.mem s.mem_domain ==>
  bytes_in_memory (n2w a) bytes
    (bootFinalState s).mem (bootFinalState s).mem_domain
Proof
  strip_tac >> imp_res_tac bootstrap_preserves_domain >> asm_rewrite_tac [] >>
  irule miscTheory.bytes_in_memory_change_mem >> qexists_tac `s.mem` >>
  simp [] >> rpt strip_tac >> CONV_TAC SYM_CONV >>
  irule bootstrap_preserves_low_memory >>
  fs [word_add_n2w,w2n_n2w,dimword_64,bootDataRam_def] >> decide_tac
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "bootstrap frame assumptions")
  [little_store_below,suffix_preserves_low_memory,copy_preserves_low_memory,
   bootstrap_copy_entry,bootstrap_preserves_low_memory,bootstrap_preserves_domain,bootstrap_preserves_bytes];
