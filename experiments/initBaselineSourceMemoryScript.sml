(* Native-entry memory agrees with the fixed source's ordinary memory. *)
Theory initBaselineSourceMemory
Ancestors initBaselineInitial initBootstrapSourceMemory
Libs preamble wordsLib
open asmSemTheory wordsTheory initSourceTheory initParamsTheory
  initSubmissionTheory initBaselineAdmissionTheory initBaselineInitialTheory
  initBootstrapSourceMemoryTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_heap_zero:
  sourceBase + 40 <= w2n a /\ w2n a < stackStart ==>
  (bootFinalState (baselineInitialAsm input)).mem a = 0w
Proof
  strip_tac >>
  `(bootFinalState (baselineInitialAsm input)).mem a =
   (baselineInitialAsm input).mem a` by
    (irule bootstrap_preserves_heap >>
     fs [baselineInitialAsm_def,sourceBase_def]) >>
  simp [baselineInitialAsm_def] >> irule initial_ram_zero >>
  simp [baseline_admitted] >>
  fs [submissionSharedDomain_def,sourceBase_def,EVAL ``stackStart``,ramStart_def,
      inputStart_def,inputEnd_def,inputSize_def,outputStart_def,
      outputEnd_def,outputSize_def]
QED
Theorem baseline_heap_word_zero:
  sourceBase + 40 <= a /\ a + 8 <= stackStart ==>
  packedBootWord (bootFinalState (baselineInitialAsm input)).mem (n2w a) = 0w
Proof
  strip_tac >>
  `!j. j < 8 ==>
    (bootFinalState (baselineInitialAsm input)).mem (n2w a+n2w j) = 0w` by
    (rpt strip_tac >> irule baseline_heap_zero >>
     `a+j < 2**64` by fs [EVAL ``stackStart``] >>
     fs [word_add_n2w,w2n_n2w,dimword_64] >> decide_tac) >>
  simp [packedBootWord_def] >> EVAL_TAC
QED
Theorem baseline_source_memory:
  a IN ordinaryDomain ==>
  Word (packedBootWord (bootFinalState (baselineInitialAsm input)).mem a) =
  sourceMemory a
Proof
  rw [ordinaryDomain_def] >>
  `8*i < 2**64` by fs [sourceBase_def,EVAL ``stackStart``,globalsWords_def] >>
  `LENGTH startupHeaders = 5` by EVAL_TAC >>
  fs [sourceMemory_def,WORD_ADD_SUB,WORD_ADD_SUB2,w2n_n2w,dimword_64] >>
  Cases_on `i < 5`
  >- (mp_tac (Q.INST [`s` |-> `baselineInitialAsm input`]
        bootstrap_final_source_headers) >>
      simp [baselineInitialAsm_def,sourceBase_def] >> metis_tac []) >>
  simp [word_add_n2w] >> irule baseline_heap_word_zero >>
  fs [word_add_n2w,sourceBase_def,EVAL ``stackStart``,globalsWords_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline source memory assumptions")
  [baseline_heap_zero,baseline_heap_word_zero,baseline_source_memory];
