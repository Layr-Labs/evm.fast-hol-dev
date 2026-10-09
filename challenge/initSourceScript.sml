(* Source state from InitE/SourceSemantics.lean. The public source semantics
   below bind the concrete accelerator specification. *)
Theory initSource
Ancestors initGuest initAccel panSem stack_remove
Libs preamble wordsLib

Definition startupHeaders_def:
  startupHeaders : word64 list =
    [0xa0020018w; 0xa0029048w; 0xa0029048w; 0x800ddd08w; 0x800de000w]
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
    let offset = w2n (address - n2w sourceBase) in
      Word (if offset MOD 8 = 0 /\ offset DIV 8 < LENGTH startupHeaders
            then EL (offset DIV 8) startupHeaders else 0w)
End
Definition sourceFfiFor_def:
  sourceFfiFor accelerator input =
    initial_ffi_state (terminalOracle accelerator) (guestHostMemory input)
End
Definition sourceInitialStateFor_def:
  sourceInitialStateFor accelerator input =
    <| locals := FEMPTY; globals := FEMPTY; structs := [];
       code := FEMPTY; eshapes := FEMPTY;
       memory := sourceMemory; memaddrs := ordinaryDomain;
       sh_memaddrs := sharedDomain; clock := 0; be := F;
       ffi := sourceFfiFor accelerator input;
       base_addr := n2w sourceBase; top_addr := n2w heapEnd |>
End
Definition sourceBehaviourFor_def:
  sourceBehaviourFor accelerator input =
    panSem$semantics_decls (sourceInitialStateFor accelerator input) «main» guestAst
End

Theorem startup_memory:
  sourceMemory (n2w sourceBase) = Word 0xa0020018w /\
  sourceMemory (n2w (sourceBase + 32)) = Word 0x800de000w /\
  sourceMemory (n2w (sourceBase + 40)) = Word 0w
Proof
  EVAL_TAC
QED

Definition sourceFfi_def:
  sourceFfi input = sourceFfiFor acceleratorBytes input
End
Definition sourceInitialState_def:
  sourceInitialState input = sourceInitialStateFor acceleratorBytes input
End
Definition sourceBehaviour_def:
  sourceBehaviour input = sourceBehaviourFor acceleratorBytes input
End
Theorem source_oracle_fixed:
  (sourceInitialState input).ffi = sourceFfi input
Proof
  simp [sourceInitialState_def,sourceInitialStateFor_def,sourceFfi_def]
QED
