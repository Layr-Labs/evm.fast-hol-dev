(* Byte installation directly from the challenge's fixed initial memory. *)
Theory initInitialCode
Ancestors initSubmission
Libs preamble wordsLib
open wordsTheory initParamsTheory miscTheory;
Theorem bytes_in_memory_from_elements:
  !bytes a bytesAt domain.
    (!i. i < LENGTH bytes ==>
      bytesAt (a+n2w i) = EL i bytes /\ a+n2w i IN domain) ==>
    bytes_in_memory a bytes bytesAt domain
Proof
  Induct >> rw [bytes_in_memory_def] >>
  TRY (first_x_assum (qspec_then `0` mp_tac) >> simp [] >> NO_TAC) >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
QED
Theorem initial_code_byte:
  initialPc <= a /\ a < initialPc + LENGTH sub.code /\ a < 2**64 /\
  ~submissionSharedDomain (n2w a) ==>
  initialMemory sub input (n2w a) = EL (a-initialPc) sub.code
Proof
  simp [initialMemory_def,w2n_n2w,dimword_64]
QED
Theorem code_region_not_shared:
  initialPc <= a /\ a < initialPc + codeSizeLimit ==>
  ~submissionSharedDomain (n2w a)
Proof
  rw [submissionSharedDomain_def,initialPc_def,codeSizeLimit_def,
      inputStart_def,inputEnd_def,inputSize_def,outputStart_def,
      outputEnd_def,outputSize_def,w2n_n2w,dimword_64] >> decide_tac
QED
Theorem program_domain_above_anchor:
  sub.anchorPc <= a /\ a < initialPc + codeSizeLimit /\
  initialPc + initMachine$ffiOffset * (sub.first+2) < sub.anchorPc ==>
  programDomain sub (n2w a)
Proof
  strip_tac >>
  `initialPc <= a /\ a < 2**64 /\ sub.anchorPc < 2**64` by
    (fs [initialPc_def,codeSizeLimit_def,initMachineTheory.ffiOffset_def] >> decide_tac) >>
  `~submissionSharedDomain (n2w a)` by metis_tac [code_region_not_shared] >>
  rewrite_tac [programDomain_def,submissionMemoryDomain_def,WORD_EQ_SUB_LADD,
    word_add_n2w,n2w_11] >>
  fs [w2n_n2w,dimword_64,initialPc_def,codeSizeLimit_def,initMachineTheory.ffiOffset_def] >>
  rpt strip_tac >> decide_tac
QED
Theorem initial_code_slice_installed:
  initialPc <= a /\
  a + LENGTH bytes <= initialPc + LENGTH sub.code /\
  a + LENGTH bytes <= initialPc + codeSizeLimit /\
  sub.anchorPc <= a /\
  initialPc + initMachine$ffiOffset * (sub.first+2) < sub.anchorPc /\
  (!i. i < LENGTH bytes ==> EL i bytes = EL (a-initialPc+i) sub.code) ==>
  bytes_in_memory (n2w a) bytes (initialMemory sub input) (programDomain sub)
Proof
  strip_tac >> irule bytes_in_memory_from_elements >> gen_tac >> strip_tac >>
  simp [word_add_n2w,IN_DEF] >>
  `initialPc <= a+i /\ a+i < initialPc+LENGTH sub.code /\
   a+i < initialPc+codeSizeLimit /\ a+i < 2**64` by
    (fs [initialPc_def,codeSizeLimit_def] >> decide_tac) >>
  `~submissionSharedDomain (n2w (a+i))` by metis_tac [code_region_not_shared] >>
  conj_tac
  >- (`initialMemory sub input (n2w (a+i)) = EL (a+i-initialPc) sub.code` by
        (irule initial_code_byte >> fs []) >>
      `a+i-initialPc = a-initialPc+i` by decide_tac >> metis_tac []) >>
  irule program_domain_above_anchor >> fs [] >> decide_tac
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "initial code assumptions")
  [bytes_in_memory_from_elements,initial_code_byte,code_region_not_shared,
   program_domain_above_anchor,initial_code_slice_installed];
