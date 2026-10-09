(* Compose native refinement and checked startup into the fixed Certificate. *)
Theory initBaselineCertificate
Ancestors initBaselineRefinement initChallengeTotal initBaselineChallengeExecution initChallenge
Libs preamble
open initBaselineRefinementTheory initChallengeTotalTheory
  initBaselineChallengeExecutionTheory initBaselineAdmissionTheory
  initCompilerMachineTheory initChallengeTheory initObservationsTheory
  initSourceTheory initParamsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = metisTools.limit := {time=SOME 10.0,infs=NONE};
Theorem baseline_native_execution:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms /\
  sourceBehaviour input = Terminate outcome events ==>
  ?k post finalFfi.
    challengeEvaluate (submissionConfig baselineSubmission) (sourceFfi input) k ms =
      (Halt outcome,post,finalFfi) /\ finalFfi.io_events = events
Proof
  strip_tac >> `sourceBehaviour input <> Fail` by simp [] >>
  drule_all baseline_native_refinement >> asm_rewrite_tac [] >>
  disch_then (mp_tac o MATCH_MP challenge_singleton_termination) >>
  simp [compiler_config_challenge_evaluation]
QED
Theorem baseline_matching_execution:
  sourceBehaviour input = Terminate outcome events /\ coveredOutcome outcome ==>
  ?steps. matchingExecutionAt baselineSubmission input outcome events steps
Proof
  strip_tac >>
  mp_tac (Q.ISPEC `sourceFfi input` (Q.GEN `ffi` baseline_challenge_execution)) >>
  strip_tac >>
  `?k post finalFfi.
    challengeEvaluate (submissionConfig baselineSubmission) (sourceFfi input) k final =
      (Halt outcome,post,finalFfi) /\ finalFfi.io_events = events` by
    metis_tac [baseline_native_execution] >>
  qexists_tac `k+n` >> simp [matchingExecutionAt_def] >>
  simp [matchingResult_refl]
QED
Theorem baseline_submission_certificate:
  submissionCertificate baselineSubmission Infinity
Proof
  simp [submissionCertificate_def,baseline_admitted,within_infinity] >>
  metis_tac [baseline_matching_execution]
QED
Theorem baseline_certificate:
  Certificate baselineRom Infinity
Proof
  rewrite_tac [Certificate_def] >> qexists_tac `baselineSubmission` >>
  simp [baseline_submission_certificate,baselineSubmission_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline certificate assumptions")
  [baseline_native_execution,baseline_matching_execution,
   baseline_submission_certificate,baseline_certificate];
