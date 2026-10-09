(* The final native-entry memory contains the exact compiled bitmap words. *)
Theory initBaselineBitmapWords
Ancestors initBaselineBitmapBytes initBootWordBytes
Libs preamble wordsLib
open wordsTheory initArtifactsTheory initBootstrapTheory initBaselineRomTheory
  initBootstrapStateTheory initBaselineInitialTheory initPackedMemoryTheory
  initBootstrapSourceMemoryTheory initBaselinePackedMemoryTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_bitmap_word:
  i < LENGTH compiledBitmaps ==>
  packedBootWord (bootFinalState (baselineInitialAsm input)).mem
    (n2w (bootDataRam+24+8*i)) = EL i compiledBitmaps
Proof
  strip_tac >>
  `!j. j < 8 ==>
    (bootFinalState (baselineInitialAsm input)).mem
      (n2w (bootDataRam+24+8*i)+n2w j) =
    EL (8*(3+i)+j) baselineInitData` by
    (rpt strip_tac >>
     `24 <= 24+8*i+j /\ 24+8*i+j < 36936` by fs [compiled_bitmap_count] >>
     mp_tac (Q.INST [`i` |-> `24+8*i+j`] baseline_final_bitmap_byte) >>
     fs [word_add_n2w,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]) >>
  rewrite_tac [packedBootWord_def] >>
  irule EQ_TRANS >>
  qexists_tac `word_of_bytes F 0w
    (GENLIST (\j. EL (8*(3+i)+j) baselineInitData) 8)` >> conj_tac
  >- (AP_TERM_TAC >> irule GENLIST_CONG >> fs []) >>
  mp_tac (Q.INST
    [`ws` |-> `[n2w initParams$sourceBase;n2w initParams$stackStart;n2w initParams$ramEnd] ++ compiledBitmaps`,
     `i` |-> `3+i`] flat_word_bytes_inverse) >>
  simp [baselineInitData_def,EL_APPEND]
QED
Theorem baseline_packed_bitmap_word:
  i < LENGTH compiledBitmaps ==>
  baselinePackedMemory input (n2w (bootDataRam+24+8*i)) =
    wordLang$Word (EL i compiledBitmaps)
Proof
  simp [baselinePackedMemory_def,packedMemory_def] >>
  metis_tac [baseline_bitmap_word,ADD_ASSOC,ADD_COMM]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline bitmap word assumptions")
  [baseline_bitmap_word,baseline_packed_bitmap_word];
