(* The bootstrap installs the fixed source headers and preserves the zero heap. *)
Theory initBootstrapSourceMemory
Ancestors initBootstrapFrame initSource
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapStartupTheory
  initBootstrapCopyTheory initBootstrapIterationTheory initBootstrapSuffixTheory
  initBootstrapStoresTheory initBootstrapStateTheory initSourceTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition packedBootWord_def:
  packedBootWord (bytesAt:word64 -> word8) (a:word64) : word64 =
    word_of_bytes F 0w (GENLIST (\j. bytesAt (a+n2w j)) 8)
End
Theorem bootstrap_source_headers:
  !i. i < 5 ==>
    packedBootWord (bootstrapStoredBytes bytesAt) (0xa1000000w+n2w (8*i)) =
    EL i startupHeaders
Proof
  CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV)) >>
  EVAL_TAC >> simp []
QED
Theorem little_store_above:
  a + 8 <= w2n x /\ a + 8 < 2**64 ==>
  littleStore 8 (n2w a) w bytesAt x = bytesAt x
Proof
  strip_tac >> irule little_store_outside >>
  rw [word_add_n2w] >> strip_tac >> fs [w2n_n2w,dimword_64] >> decide_tac
QED
Theorem suffix_preserves_heap:
  0xa1000028 <= w2n x ==>
  bootstrapStoredBytes bytesAt x = bytesAt x
Proof
  strip_tac >>
  `!a w bytesAt. a+8 <= 0xa1000028 ==>
     littleStore 8 (n2w a) w bytesAt x = bytesAt x` by
    (rpt strip_tac >> irule little_store_above >> simp [] >> decide_tac) >>
  simp [bootstrapStoredBytes_def]
QED
Theorem copy_preserves_heap:
  ~s.be /\ s.pc = n2w initParams$initialPc /\ bootDataEnd <= w2n x ==>
  (bootCopyState s).mem x = s.mem x
Proof
  strip_tac >> simp [bootCopyState_def] >>
  imp_res_tac bootstrap_startup_effect >>
  `(copyIterations 4617 (bootRun bootstrapPrefix s)).mem x =
   (bootRun bootstrapPrefix s).mem x` by
    (irule baseline_copy_outside >> fs [] >>
     rw [bootDataRam_def] >> strip_tac >>
     fs [bootDataRam_def,bootDataEnd_def,w2n_n2w,dimword_64] >> decide_tac) >>
  fs []
QED
Theorem bootstrap_preserves_heap:
  ~s.be /\ s.pc = n2w initParams$initialPc /\ 0xa1000028 <= w2n x ==>
  (bootFinalState s).mem x = s.mem x
Proof
  strip_tac >> imp_res_tac bootstrap_copy_entry >>
  simp [bootFinalState_def,bootstrap_suffix_memory,suffix_preserves_heap] >>
  irule copy_preserves_heap >> fs [bootDataEnd_def]
QED
Theorem bootstrap_final_source_headers:
  ~s.be /\ s.pc = n2w initParams$initialPc ==>
  !i. i < 5 ==>
    packedBootWord (bootFinalState s).mem (0xa1000000w+n2w (8*i)) =
    EL i startupHeaders
Proof
  strip_tac >> imp_res_tac bootstrap_copy_entry >>
  simp [bootFinalState_def,bootstrap_suffix_memory,
        SIMP_RULE (srw_ss()) [] bootstrap_source_headers]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "source-memory frame assumptions")
  [bootstrap_source_headers,little_store_above,suffix_preserves_heap,
   copy_preserves_heap,bootstrap_preserves_heap,bootstrap_final_source_headers];
