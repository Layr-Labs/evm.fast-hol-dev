(* Regression checks on the imported guest, using synthetic length headers.
   Payload reads deliberately fail, so no large host input list is allocated. *)
Theory initInputArenaChecks
Ancestors initGuest initHost initObservations panSem
Libs preamble wordsLib

Definition arenaCheckHost_def:
  arenaCheckHost length (address:word64) =
    if inputStart + 8 <= w2n address /\ w2n address < inputStart + 16 then
      SOME (EL (w2n address - inputStart - 8) (leBytes (n2w length)))
    else if inputStart + 16 <= w2n address /\ w2n address < inputEnd then NONE
    else guestHostMemory [] address
End
Definition arenaCheckDecls_def:
  arenaCheckDecls =
    [guestGlobal_heap_ptr; guestGlobal_journal_n; guestExn_TrapErr;
     guestGlobal_scratch_ptr; guestGlobal_frame_mem_ptr;
     guestFn_mem_init; guestFn_alloc; guestFn_trap_with; guestFn_input_blob]
End
Definition arenaCheckRun_def:
  arenaCheckRun length =
    let s = <| locals := FEMPTY; globals := FEMPTY; structs := [];
      code := FEMPTY; eshapes := FEMPTY; memory := (\a. Word 0w);
      memaddrs := UNIV; sh_memaddrs := UNIV; clock := 100; be := F;
      base_addr := n2w sourceBase; top_addr := n2w heapEnd;
      ffi := initial_ffi_state terminalOracle
        (arenaCheckHost length) |> in
    case evaluate_decls s arenaCheckDecls of
      NONE => NONE
    | SOME st => SOME (evaluate
        (Seq (Call (SOME (NONE,NONE)) «mem_init» [])
             (Call NONE «input_blob» []), st))
End
Definition arenaCheckOversized_def:
  arenaCheckOversized length =
    case arenaCheckRun length of
      SOME (SOME (FinalFFI (Final_event name conf bytes result)), st) =>
        name = ExtCall «trap» /\ LENGTH conf = 8 /\
        result = FFI_failed /\
        st.ffi.ffi_state (n2w (outputStart + 33)) = SOME 8w /\
        FLOOKUP st.globals «heap_ptr» = SOME (ValWord 2701131776w) /\
        coveredOutcome (FFI_outcome (Final_event name conf bytes result))
    | _ => F
End
Definition arenaCheckHeapLimited_def:
  arenaCheckHeapLimited length =
    case arenaCheckRun length of
      SOME (SOME (FinalFFI (Final_event name conf bytes result)), st) =>
        name = ExtCall «trap» /\ LENGTH conf = 1 /\
        result = FFI_failed /\
        st.ffi.ffi_state (n2w (outputStart + 33)) = SOME 1w /\
        FLOOKUP st.globals «heap_ptr» = SOME (ValWord 2701131776w) /\
        ~coveredOutcome (FFI_outcome (Final_event name conf bytes result))
    | _ => F
End
Definition arenaCheckInRange_def:
  arenaCheckInRange length =
    case arenaCheckRun length of
      SOME (SOME (FinalFFI (Final_event name conf bytes result)), st) =>
        name = SharedMem MappedRead /\ result = FFI_failed /\
        wordOfLeBytes bytes = n2w (inputStart + 16)
    | _ => F
End
Theorem oversized_rejected_before_allocation:
  EVERY arenaCheckOversized
    [1073741809; 2 ** 35; 2 ** 64 - 8; 2 ** 64 - 1]
Proof
  EVAL_TAC
QED
Theorem in_range_reaches_payload:
  EVERY arenaCheckInRange [1; 251658231; 251658232]
Proof
  EVAL_TAC
QED

(* The arena is larger than the guest heap. input_blob allocates len+8;
   arena-valid lengths above 0x0f000000-8 fail with the existing resource trap. *)
Theorem arena_valid_but_heap_limited:
  EVERY arenaCheckHeapLimited [251658233; 1073741807; 1073741808]
Proof
  EVAL_TAC
QED
