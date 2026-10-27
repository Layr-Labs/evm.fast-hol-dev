(* Fixed shared-memory geometry and the identity interference oracle. *)
Theory initSharedDomain
Ancestors initDataDomain initCompilerMachine
Libs preamble wordsLib
open wordsTheory alignmentTheory asmPropsTheory initParamsTheory
  initSubmissionTheory initCompilerMachineTheory initMachineTheory
  initBitmapDomainTheory;
Theorem shared_domain_align_closed:
  byte_align a IN submissionSharedDomain ==> a IN submissionSharedDomain
Proof
  strip_tac >>
  mp_tac (Q.INST [`lo` |-> `n2w inputStart:word64`,
                 `hi` |-> `n2w inputEnd:word64`]
    (INST_TYPE [alpha |-> ``:64``] aligned_interval_closed)) >>
  mp_tac (Q.INST [`lo` |-> `n2w outputStart:word64`,
                 `hi` |-> `n2w outputEnd:word64`]
    (INST_TYPE [alpha |-> ``:64``] aligned_interval_closed)) >>
  fs [IN_DEF,submissionSharedDomain_def,inputStart_def,inputEnd_def,inputSize_def,
      outputStart_def,outputEnd_def,outputSize_def,byte_aligned_def,aligned_w2n,
      w2n_n2w,dimword_64,dimindex_64] >> metis_tac []
QED
Theorem program_shared_disjoint:
  DISJOINT (programDomain s) submissionSharedDomain
Proof
  rw [IN_DISJOINT,IN_DEF,programDomain_def,submissionMemoryDomain_def] >>
  metis_tac []
QED
Theorem compiler_identity_interference:
  interference_ok (compilerMachineConfig s).next_interfer
    ((compilerMachineConfig s).target.proj dm)
Proof
  simp [interference_ok_def,compilerMachineConfig_def,submissionConfig_def,
        challengeMachineConfig_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "shared domain assumptions")
  [shared_domain_align_closed,program_shared_disjoint,compiler_identity_interference];
