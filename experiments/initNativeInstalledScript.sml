(* Exact compiled native bytes are installed by the fixed initial memory,
   and remain installed after the bootstrap state updates. *)
Theory initNativeInstalled
Ancestors initBaselineRom initInitialCode initBootstrapFrame
Libs preamble wordsLib
open wordsTheory initParamsTheory initBootstrapTheory initBytecodeTheory
  initSubmissionTheory initMachineTheory initBootstrapStateTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem native_rom_elements:
  !i. i < LENGTH compiledBytes ==>
    EL i compiledBytes = EL (baselineNativePc-initialPc+i) baselineRom
Proof
  rpt strip_tac >>
  `i + (baselineNativePc-initialPc) < LENGTH baselineRom` by
    (fs [compiled_byte_count,baseline_rom_length,baselineNativePc_def,initialPc_def] >> decide_tac) >>
  mp_tac (AP_TERM ``EL (i:num) : word8 list -> word8`` native_image_in_rom) >>
  simp [EL_TAKE,EL_DROP,ADD_COMM]
QED
Theorem native_initially_installed:
  candidateSubmission.code = baselineRom /\ candidateSubmission.anchorPc = baselineNativePc /\
  initialPc + ffiOffset * (candidateSubmission.first+2) < baselineNativePc ==>
  bytes_in_memory (n2w baselineNativePc) compiledBytes
    (initialMemory candidateSubmission input) (programDomain candidateSubmission)
Proof
  strip_tac >> irule initial_code_slice_installed >>
  simp [native_rom_elements,compiled_byte_count,baseline_rom_length,
    initialPc_def,baselineNativePc_def,codeSizeLimit_def]
QED
Theorem native_installed_after_bootstrap:
  candidateSubmission.code = baselineRom /\ candidateSubmission.anchorPc = baselineNativePc /\
  initialPc + ffiOffset * (candidateSubmission.first+2) < baselineNativePc /\
  ~s.be /\ s.pc = n2w initialPc /\
  s.mem = initialMemory candidateSubmission input /\ s.mem_domain = programDomain candidateSubmission ==>
  bytes_in_memory (n2w baselineNativePc) compiledBytes
    (bootFinalState s).mem (bootFinalState s).mem_domain
Proof
  strip_tac >>
  `bytes_in_memory (n2w baselineNativePc) compiledBytes
    (initialMemory candidateSubmission input) (programDomain candidateSubmission)` by
    (irule native_initially_installed >> fs []) >>
  irule bootstrap_preserves_bytes >>
  fs [compiled_byte_count,baselineNativePc_def,bootDataRam_def]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "native installation assumptions")
  [native_rom_elements,native_initially_installed,native_installed_after_bootstrap];
