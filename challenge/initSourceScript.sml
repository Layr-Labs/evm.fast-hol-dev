(* Source state from the software guest revision of InitE/SourceSemantics.lean. *)
Theory initSource
Ancestors initGuest initHost panSem stack_remove
Libs preamble wordsLib

Definition startupHeaders_def:
  startupHeaders : word64 list =
    [0xa0020018w; 0xa0028ff0w; 0xa0028ff0w; 0x800f0134w; 0x800f1000w]
End
Definition ordinaryDomain_def:
  ordinaryDomain =
    {n2w sourceBase + n2w (8 * i) : word64 |
     i < (stackStart - sourceBase) DIV 8 - globalsWords}
End
Definition sharedDomain_def:
  sharedDomain (address : word64) =
    (byte_align address = address /\
     ((inputStart <= w2n address /\ w2n address < inputEnd) \/
      (outputStart <= w2n address /\ w2n address < outputEnd)))
End
Definition sourceMemory_def:
  sourceMemory (address : word64) =
    Word (if sourceBase <= w2n address /\ w2n address < sourceBase + 40
          then EL ((w2n address - sourceBase) DIV 8) startupHeaders else 0w)
End
Definition sourceFfiFor_def:
  sourceFfiFor input =
    initial_ffi_state terminalOracle (guestHostMemory input)
End
Definition sourceInitialStateFor_def:
  sourceInitialStateFor input =
    <| locals := FEMPTY; globals := FEMPTY; structs := [];
       code := FEMPTY; eshapes := FEMPTY;
       memory := sourceMemory; memaddrs := ordinaryDomain;
       sh_memaddrs := sharedDomain; clock := 0; be := F;
       ffi := sourceFfiFor input;
       base_addr := n2w sourceBase; top_addr := n2w heapEnd |>
End
Definition sourceBehaviourFor_def:
  sourceBehaviourFor input =
    panSem$semantics_decls (sourceInitialStateFor input) «main» guestAst
End

Theorem startup_memory:
  sourceMemory (n2w sourceBase) = Word 0xa0020018w /\
  sourceMemory (n2w (sourceBase + 1)) = Word 0xa0020018w /\
  sourceMemory (n2w (sourceBase + 32)) = Word 0x800f1000w /\
  sourceMemory (n2w (sourceBase + 40)) = Word 0w
Proof
  EVAL_TAC
QED

Definition sourceFfi_def:
  sourceFfi input = sourceFfiFor input
End
Definition sourceInitialState_def:
  sourceInitialState input = sourceInitialStateFor input
End
Definition sourceBehaviour_def:
  sourceBehaviour input = sourceBehaviourFor input
End
Theorem source_oracle_fixed:
  (sourceInitialState input).ffi = sourceFfi input
Proof
  simp [sourceInitialState_def,sourceInitialStateFor_def,sourceFfi_def]
QED
