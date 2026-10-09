(* Fixed certificate proposition. Only bytes, score and admitted layout
   metadata vary; the source, oracle, machine construction and evaluator do not. *)
Theory initChallenge
Ancestors initSubmission initGas initObservations
Libs preamble
Definition matchingExecutionAt_def:
  matchingExecutionAt s input outcome events steps =
    (?targetOutcome post finalFfi.
      challengeEvaluate (submissionConfig s) (sourceFfi input) steps (initialState s input) =
        (Halt targetOutcome,post,finalFfi) /\
      matchingResult (terminalOracle acceleratorBytes) (guestHostMemory input)
        outcome events targetOutcome finalFfi.io_events)
End
Definition submissionCertificate_def:
  submissionCertificate s claimed =
    (admitted s /\ !input outcome events.
      declaredGasLimit input <= gasLimit /\
      sourceBehaviour input = Terminate outcome events /\ coveredOutcome outcome ==>
      within claimed (matchingExecutionAt s input outcome events))
End
(* Layout is an existential witness bound by admission. Its choice cannot
   replace the target evaluator, fixed oracle, source program, bytes or score. *)
Definition Certificate_def:
  Certificate bytes claimed =
    (?s. s.code = bytes /\ submissionCertificate s claimed)
End
Theorem certificate_requires_admitted_bytes:
  Certificate bytes score ==> ?s. s.code = bytes /\ admitted s
Proof
  rw [Certificate_def,submissionCertificate_def] >> metis_tac []
QED
Theorem infinity_requires_termination:
  submissionCertificate s Infinity /\ declaredGasLimit input <= gasLimit /\
  sourceBehaviour input = Terminate outcome events /\ coveredOutcome outcome ==>
  ?steps. matchingExecutionAt s input outcome events steps
Proof
  rw [submissionCertificate_def] >>
  first_x_assum (qspecl_then [`input`,`outcome`,`events`] mp_tac) >>
  simp [initParamsTheory.within_infinity]
QED

Theorem empty_bytes_rejected:
  ~Certificate [] score
Proof
  simp [Certificate_def,submissionCertificate_def,initSubmissionTheory.admitted_def]
QED
