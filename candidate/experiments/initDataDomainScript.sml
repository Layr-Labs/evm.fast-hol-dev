(* The ordinary data domains used at native entry. *)
Theory initDataDomain
Ancestors initBitmapDomain initSubmission
Libs preamble wordsLib
open wordsTheory alignmentTheory initParamsTheory initBootstrapTheory;
Definition heapStackDomain_def:
  heapStackDomain = {a:word64 | sourceBase <= w2n a /\ w2n a < ramEnd}
End
Theorem heap_stack_align_closed:
  byte_align a IN heapStackDomain ==> a IN heapStackDomain
Proof
  strip_tac >>
  mp_tac (Q.INST [`lo` |-> `n2w sourceBase:word64`,
                 `hi` |-> `n2w ramEnd:word64`]
    (INST_TYPE [alpha |-> ``:64``] aligned_interval_closed)) >>
  fs [heapStackDomain_def,sourceBase_def,ramEnd_def,ramStart_def,ramSize_def,
      byte_aligned_def,aligned_w2n,w2n_n2w,dimword_64,dimindex_64]
QED
Theorem data_domain_align_closed:
  byte_align a IN heapStackDomain UNION bitmapDomain ==>
  a IN heapStackDomain UNION bitmapDomain
Proof
  metis_tac [IN_UNION,heap_stack_align_closed,bitmap_domain_align_closed]
QED
Theorem data_domains_disjoint:
  DISJOINT heapStackDomain bitmapDomain
Proof
  rw [IN_DISJOINT,heapStackDomain_def,bitmapDomain_def,
      sourceBase_def,bootDataRam_def,bootDataEnd_def] >> decide_tac
QED
Theorem data_domains_not_shared:
  DISJOINT (heapStackDomain UNION bitmapDomain) submissionSharedDomain
Proof
  rw [IN_DISJOINT,IN_DEF,heapStackDomain_def,bitmapDomain_def,
      submissionSharedDomain_def,sourceBase_def,bootDataRam_def,bootDataEnd_def,
      inputStart_def,inputEnd_def,inputSize_def,
      outputStart_def,outputEnd_def,outputSize_def] >> decide_tac
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "data domain assumptions")
  [heap_stack_align_closed,data_domain_align_closed,data_domains_disjoint,
   data_domains_not_shared];
