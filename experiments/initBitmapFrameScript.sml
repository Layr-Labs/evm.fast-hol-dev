(* Exact copied bitmap bytes survive the final bootstrap header stores. *)
Theory initBitmapFrame
Ancestors initBootstrapSourceMemory
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapFrameTheory
  initBootstrapStartupTheory initBootstrapStateTheory initBootstrapSuffixTheory
  initBootstrapStoresTheory initBootstrapCopyTheory;
Theorem suffix_preserves_bitmap_memory:
  0xa0020018 <= w2n x /\ w2n x < 0xa1000000 ==>
  bootstrapStoredBytes bytesAt x = bytesAt x
Proof
  strip_tac >>
  `!a w bytesAt. a+8 <= 0xa0020018 ==>
     littleStore 8 (n2w a) w bytesAt x = bytesAt x` by
    (rpt strip_tac >> irule little_store_above >> simp [] >> decide_tac) >>
  `!a w bytesAt. 0xa1000000 <= a /\ a+8 < 2**64 ==>
     littleStore 8 (n2w a) w bytesAt x = bytesAt x` by
    (rpt strip_tac >> irule little_store_below >> decide_tac) >>
  simp [bootstrapStoredBytes_def]
QED
Theorem bootstrap_final_bitmap_bytes:
  ~s.be /\ s.pc = n2w initParams$initialPc /\ 24 <= i /\ i < 36936 ==>
  (bootFinalState s).mem (n2w (bootDataRam+i)) =
  s.mem (n2w (bootDataRom+i))
Proof
  strip_tac >> imp_res_tac bootstrap_copy_entry >>
  `0xa0020018 <= w2n (n2w (bootDataRam+i):word64) /\
   w2n (n2w (bootDataRam+i):word64) < 0xa1000000` by
    (fs [bootDataRam_def,w2n_n2w,dimword_64] >> decide_tac) >>
  gvs [] >>
  simp [bootFinalState_def,bootstrap_suffix_memory,suffix_preserves_bitmap_memory] >>
  simp [bootCopyState_def] >>
  mp_tac (Q.INST [`s` |-> `bootRun bootstrapPrefix s`] baseline_copy_all_bytes) >>
  imp_res_tac bootstrap_startup_effect >> simp [] >>
  disch_then (qspec_then `i` mp_tac) >> simp []
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "bitmap copy frame assumptions")
  [suffix_preserves_bitmap_memory,bootstrap_final_bitmap_bytes];
