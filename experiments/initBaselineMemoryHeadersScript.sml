(* Fixed source headers expressed in the compiler installation layout. *)
Theory initBaselineMemoryHeaders
Ancestors initBaselinePackedMemory initArtifacts
Libs preamble wordsLib
open wordsTheory initBootstrapSourceMemoryTheory initBaselineInitialTheory
  initPackedMemoryTheory initBootstrapTheory initParamsTheory initSourceTheory
  initBytecodeTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_packed_headers:
  !i. i < 5 ==>
  baselinePackedMemory input (0xa1000000w+n2w (8*i)) =
    wordLang$Word (EL i startupHeaders)
Proof
  mp_tac (Q.INST [`s` |-> `baselineInitialAsm input`] bootstrap_final_source_headers) >>
  simp [baselineInitialAsm_def,baselinePackedMemory_def,packedMemory_def]
QED
Theorem baseline_installation_headers:
  baselinePackedMemory input (n2w sourceBase) = wordLang$Word (n2w (bootDataRam+24)) /\
  baselinePackedMemory input (n2w sourceBase+8w) =
    wordLang$Word (n2w (bootDataRam+24)+8w*n2w (LENGTH compiledBitmaps)) /\
  baselinePackedMemory input (n2w sourceBase+16w) =
    wordLang$Word (n2w (bootDataRam+24)+8w*n2w (LENGTH compiledBitmaps)) /\
  baselinePackedMemory input (n2w sourceBase+24w) =
    wordLang$Word (n2w baselineNativePc+n2w (LENGTH compiledBytes)) /\
  baselinePackedMemory input (n2w sourceBase+32w) =
    wordLang$Word (n2w baselineNativePc+n2w 760+n2w (LENGTH compiledBytes))
Proof
  mp_tac baseline_packed_headers >>
  CONV_TAC (LAND_CONV (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV))) >>
  simp [startupHeaders_def,compiled_bitmap_count,compiled_byte_count,
        sourceBase_def,bootDataRam_def,baselineNativePc_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline memory header assumptions")
  [baseline_packed_headers,baseline_installation_headers];
