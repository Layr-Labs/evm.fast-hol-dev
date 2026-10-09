(* Connect copied native-entry bitmap bytes to the exact ROM data image. *)
Theory initBaselineBitmapBytes
Ancestors initBitmapFrame initBaselinePackedMemory
Libs preamble wordsLib
open wordsTheory initParamsTheory initBootstrapTheory initBaselineRomTheory
  initSubmissionTheory initBaselineAdmissionTheory initBaselineInitialTheory
  initBootstrapStateTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem data_rom_elements:
  !i. i < 36936 ==>
    EL i baselineInitData = EL (bootDataRom-initialPc+i) baselineRom
Proof
  rpt strip_tac >>
  `i + (bootDataRom-initialPc) < LENGTH baselineRom` by
    fs [baseline_rom_length,bootDataRom_def,initialPc_def] >>
  mp_tac (AP_TERM ``EL (i:num) : word8 list -> word8`` data_image_in_rom) >>
  simp [EL_DROP,ADD_COMM]
QED
Theorem baseline_initial_data_byte:
  i < 36936 ==>
  initialMemory baselineSubmission input (n2w (bootDataRom+i)) = EL i baselineInitData
Proof
  strip_tac >>
  `w2n (n2w (bootDataRom+i):word64) = bootDataRom+i` by
    fs [bootDataRom_def,w2n_n2w,dimword_64] >>
  `~submissionSharedDomain (n2w (bootDataRom+i):word64)` by
    fs [submissionSharedDomain_def,bootDataRom_def,inputStart_def,inputEnd_def,
        inputSize_def,outputStart_def,outputEnd_def,outputSize_def] >>
  simp [initialMemory_def,baselineSubmission_def,baseline_rom_length] >>
  mp_tac (Q.SPEC `i` data_rom_elements) >>
  fs [bootDataRom_def,initialPc_def]
QED
Theorem baseline_final_bitmap_byte:
  24 <= i /\ i < 36936 ==>
  (bootFinalState (baselineInitialAsm input)).mem (n2w (bootDataRam+i)) =
  EL i baselineInitData
Proof
  strip_tac >>
  mp_tac (Q.INST [`s` |-> `baselineInitialAsm input`] bootstrap_final_bitmap_bytes) >>
  simp [baselineInitialAsm_def] >>
  metis_tac [baseline_initial_data_byte,ADD_COMM]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline bitmap byte assumptions")
  [data_rom_elements,baseline_initial_data_byte,baseline_final_bitmap_byte];
