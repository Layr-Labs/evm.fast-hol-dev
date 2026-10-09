(* Observation rules from InitE/Observations.lean. The oracle and initial
   host are parameters here; the fixed challenge must instantiate them. *)
Theory initObservations
Ancestors initParams ffi
Libs preamble

Definition replayOracle_def:
  replayOracle oracle initial events =
    FOLDL (\host event.
      case event of IO_event name conf bytes =>
        case oracle name host conf (MAP FST bytes) of
          Oracle_return next result => next
        | Oracle_final outcome => host) initial events
End

Definition outputByte_def:
  outputByte (host : word64 -> word8 option) offset =
    case host (n2w outputStart + n2w offset) of
      NONE => 0w | SOME b => b
End

Definition normalHalt_def:
  normalHalt Success = T /\
  normalHalt Resource_limit_hit = F /\
  normalHalt (FFI_outcome (Final_event name conf bytes result)) =
    (name = ExtCall «halt» /\ result = FFI_failed)
End

Definition coveredOutcome_def:
  coveredOutcome Success = T /\
  coveredOutcome Resource_limit_hit = F /\
  coveredOutcome (FFI_outcome (Final_event name conf bytes result)) =
    (result = FFI_failed /\
     (name <> ExtCall «trap» \/
      (LENGTH conf <> 1 /\ LENGTH conf <> 6 /\ LENGTH conf <> 7)))
End

Definition acceptedOutput_def:
  acceptedOutput oracle initial outcome events =
    (normalHalt outcome /\
     outputByte (replayOracle oracle initial events) 32 = 1w)
End

Definition matchingResult_def:
  matchingResult oracle initial sourceOutcome sourceEvents targetOutcome targetEvents =
    if acceptedOutput oracle initial sourceOutcome sourceEvents then
      acceptedOutput oracle initial targetOutcome targetEvents /\
      (!offset. offset < outputSize ==>
        outputByte (replayOracle oracle initial sourceEvents) offset =
        outputByte (replayOracle oracle initial targetEvents) offset)
    else coveredOutcome targetOutcome /\
         ~acceptedOutput oracle initial targetOutcome targetEvents
End

Theorem matchingResult_refl:
  coveredOutcome outcome ==>
  matchingResult oracle initial outcome events outcome events
Proof
  rw [matchingResult_def]
QED

Theorem infinity_requires_finite_execution:
  within Infinity (\steps. ?outcome state ffi.
    execute steps = (outcome,state,ffi) /\ matches outcome ffi) ==>
  ?steps outcome state ffi.
    execute steps = (outcome,state,ffi) /\ matches outcome ffi
Proof
  simp [within_infinity]
QED
