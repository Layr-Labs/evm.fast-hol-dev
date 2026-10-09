Theory initParams
Ancestors cv_std
Libs cv_transLib

Datatype:
  budget = Finite num | Infinity
End

Definition allows_def:
  allows (Finite bound) steps = (steps <= bound) /\
  allows Infinity steps = T
End

Definition within_def:
  within b terminates_at = ?steps. allows b steps /\ terminates_at steps
End

Theorem within_infinity:
  within Infinity terminates_at <=> ?steps. terminates_at steps
Proof
  simp [within_def, allows_def]
QED

Definition initialPc_def:
  initialPc : num = 0x80000000
End
val _ = cv_trans initialPc_def;

Definition codeSizeLimit_def:
  codeSizeLimit : num = 0x08000000
End
val _ = cv_trans codeSizeLimit_def;

Definition inputStart_def:
  inputStart : num = 0x40000000
End
val _ = cv_trans inputStart_def;

Definition inputSize_def:
  inputSize : num = 0x08000000
End
val _ = cv_trans inputSize_def;

Definition inputEnd_def:
  inputEnd : num = inputStart + inputSize
End
val _ = cv_trans inputEnd_def;

Definition outputStart_def:
  outputStart : num = 0xa0410000
End
val _ = cv_trans outputStart_def;

Definition outputSize_def:
  outputSize : num = 0x10000
End
val _ = cv_trans outputSize_def;

Definition outputEnd_def:
  outputEnd : num = outputStart + outputSize
End
val _ = cv_trans outputEnd_def;

Definition ramStart_def:
  ramStart : num = 0xa0000000
End
val _ = cv_trans ramStart_def;

Definition ramSize_def:
  ramSize : num = 29 * 1024 * 1024 * 1024
End
val _ = cv_trans ramSize_def;

Definition ramEnd_def:
  ramEnd : num = ramStart + ramSize
End
val _ = cv_trans ramEnd_def;

Definition sourceBase_def:
  sourceBase : num = 0xa1000000
End
val _ = cv_trans sourceBase_def;

Definition scratchStart_def:
  scratchStart : num = sourceBase + 4096
End
val _ = cv_trans scratchStart_def;

Definition scratchEnd_def:
  scratchEnd : num = 0xa1c00000
End
val _ = cv_trans scratchEnd_def;

Definition heapStart_def:
  heapStart : num = scratchEnd
End
val _ = cv_trans heapStart_def;

Definition stackSize_def:
  stackSize : num = 16 * 1024 * 1024
End
val _ = cv_trans stackSize_def;

Definition stackStart_def:
  stackStart : num = ramEnd - stackSize
End
val _ = cv_trans stackStart_def;

Definition globalsWords_def:
  globalsWords : num = 93
End
val _ = cv_trans globalsWords_def;

Definition heapEnd_def:
  heapEnd : num = stackStart - globalsWords * 8
End
val _ = cv_trans heapEnd_def;

Definition gasLimit_def:
  gasLimit : num = 200000000
End
val _ = cv_trans gasLimit_def;

Theorem regions_disjoint:
  inputEnd <= initialPc /\ initialPc + codeSizeLimit <= ramStart /\
  ramStart <= outputStart /\ outputEnd <= sourceBase /\ sourceBase < scratchStart /\
  scratchStart < scratchEnd /\ scratchEnd <= heapStart /\
  heapStart < heapEnd /\ heapEnd + globalsWords * 8 = stackStart /\ stackStart < ramEnd
Proof
  CONV_TAC cv_eval
QED

Theorem layout_alignment:
  ramEnd MOD 4096 = 0 /\ heapEnd MOD 8 = 0 /\ 7480 * 8 < stackSize
Proof
  CONV_TAC cv_eval
QED
