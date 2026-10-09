(* Concrete word memory for the compiler's native-entry installation witness. *)
Theory initBaselinePackedMemory
Ancestors initPackedMemory initBaselineSourceMemory crep_to_loopProof
Libs preamble wordsLib
open initPackedMemoryTheory initBaselineSourceMemoryTheory initSourceTheory
  initBootstrapStateTheory initBaselineInitialTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition baselinePackedMemory_def:
  baselinePackedMemory input =
    packedMemory (bootFinalState (baselineInitialAsm input)).mem
End
Theorem baseline_packed_source_memory:
  a IN ordinaryDomain ==>
  baselinePackedMemory input a =
    crep_to_loopProof$wlab_wloc (sourceMemory a)
Proof
  strip_tac >>
  `sourceMemory a = panSem$Word
     (packedBootWord (bootFinalState (baselineInitialAsm input)).mem a)` by
    metis_tac [baseline_source_memory] >>
  simp [baselinePackedMemory_def,packedMemory_def,
        crep_to_loopProofTheory.wlab_wloc_def]
QED
Theorem baseline_packed_byte_memory:
  !a. ?w. (bootFinalState (baselineInitialAsm input)).mem a = get_byte a w F /\
    baselinePackedMemory input (byte_align a) = wordLang$Word w
Proof
  simp [baselinePackedMemory_def,packed_memory_relation]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline packed-memory assumptions")
  [baseline_packed_source_memory,baseline_packed_byte_memory];
