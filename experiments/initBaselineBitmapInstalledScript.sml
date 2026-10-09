(* Exact bitmap allocation in the compiler's separated-memory form. *)
Theory initBaselineBitmapInstalled
Ancestors initBaselineBitmapWords initBitmapDomain initWordListMemory
Libs preamble wordsLib
open wordsTheory miscTheory set_sepTheory stack_removeProofTheory
  initArtifactsTheory initBootstrapTheory initBaselinePackedMemoryTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_bitmap_word_list:
  word_list (n2w (bootDataRam+24):word64) (MAP wordLang$Word compiledBitmaps)
    (fun2set (baselinePackedMemory input, byte_aligned INTER bitmapDomain))
Proof
  rewrite_tac [bitmap_word_domain] >>
  `IMAGE (\i. n2w (bootDataRam+24+8*i):word64) (count 4614) =
   IMAGE (\i. n2w (bootDataRam+24)+n2w i*bytes_in_word:word64)
     (count (LENGTH (MAP wordLang$Word compiledBitmaps)))` by
    simp [compiled_bitmap_count,bytes_in_word_def,word_mul_n2w,word_add_n2w] >>
  pop_assum (fn th => rewrite_tac [th]) >>
  irule indexed_word_list_memory >>
  simp [good_dimindex_def,dimindex_64,dimword_64,bytes_in_word_def,
        bootDataRam_def,compiled_bitmap_count,w2n_n2w] >>
  rpt strip_tac >>
  mp_tac (Q.INST [`i` |-> `i`] baseline_packed_bitmap_word) >>
  simp [compiled_bitmap_count,EL_MAP,bytes_in_word_def,word_mul_n2w,
        word_add_n2w,bootDataRam_def]
QED
Theorem baseline_bitmap_allocation:
  (word_list (n2w (bootDataRam+24):word64) (MAP wordLang$Word compiledBitmaps) *
   word_list_exists (n2w bootDataEnd) 0)
    (fun2set (baselinePackedMemory input, byte_aligned INTER bitmapDomain))
Proof
  simp [word_list_exists_thm,SEP_CLAUSES,baseline_bitmap_word_list]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "bitmap installation assumptions")
  [baseline_bitmap_word_list,baseline_bitmap_allocation];
