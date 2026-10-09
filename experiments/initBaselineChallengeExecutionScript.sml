(* Bootstrap execution by the fixed challenge evaluator, with all checks. *)
Theory initBaselineChallengeExecution
Ancestors initBaselineRestrictedExecution initBootstrapChallengeTrace
Libs preamble wordsLib
open initBaselineInitialTheory initBootstrapChallengeTraceTheory
  initChallengeExecutionTheory initSubmissionTheory initMachineTheory
  initBaselineAdmissionTheory initBootstrapStateTheory initBootstrapStepTheory
  initRestrictedEncoderTheory initRestrictedStepTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem baseline_challenge_trace:
  RTC (challengeAsmEdge (submissionConfig baselineSubmission))
    (baselineInitialAsm input) (bootFinalState (baselineInitialAsm input))
Proof
  irule bootstrap_challenge_trace >>
  simp [baselineInitialAsm_def,bootstrapRomInvariant_def] >>
  metis_tac [baseline_bootstrap_domains,arithmeticTheory.ADD_COMM]
QED
Theorem baseline_target:
  (submissionConfig baselineSubmission).target = restrictedTarget
Proof
  simp [submissionConfig_def,challengeMachineConfig_def]
QED
Theorem baseline_identity_interference:
  identityNextInterference (submissionConfig baselineSubmission)
Proof
  simp [submissionConfig_def,challenge_identity_interference]
QED
Theorem baseline_challenge_execution:
  ?n final.
    (!k. challengeEvaluate (submissionConfig baselineSubmission) ffi (k+n)
           (initialState baselineSubmission input) =
         challengeEvaluate (submissionConfig baselineSubmission) ffi k final) /\
    target_state_rel restrictedTarget
      (bootFinalState (baselineInitialAsm input)) final
Proof
  mp_tac (INST_TYPE [beta |-> alpha]
    (Q.ISPEC `submissionConfig baselineSubmission`
      (GEN_ALL challenge_rtc_execution))) >>
  simp [baseline_target,restricted_encoder_correct,baseline_identity_interference] >>
  disch_then (qspecl_then
    [`baselineInitialAsm input`,`bootFinalState (baselineInitialAsm input)`] mp_tac) >>
  simp [baseline_challenge_trace] >>
  disch_then (qspecl_then [`initialState baselineSubmission input`,`ffi`] mp_tac) >>
  simp [restricted_target_state_relation,baseline_initial_target_relation]
QED
Theorem baseline_bootstrap_timeout:
  ?n final.
    challengeEvaluate (submissionConfig baselineSubmission) ffi n
      (initialState baselineSubmission input) = (TimeOut,final,ffi) /\
    target_state_rel restrictedTarget
      (bootFinalState (baselineInitialAsm input)) final
Proof
  strip_assume_tac baseline_challenge_execution >>
  qexists_tac `n` >> qexists_tac `final` >> simp [] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp [challenge_timeout]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline challenge execution assumptions")
  [baseline_challenge_trace,baseline_target,baseline_identity_interference,
   baseline_challenge_execution,baseline_bootstrap_timeout];
