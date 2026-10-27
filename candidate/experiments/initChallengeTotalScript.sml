(* Totality of observable fixed-challenge semantics.
   Adapted from pinned CakeML targetProps; see ../CAKEML-LICENSE. *)
Theory initChallengeTotal
Ancestors initChallengeSemantics
Libs preamble
open initChallengeSemanticsTheory initChallengeClockTheory initMachineTheory
  targetSemTheory ffiTheory lprefix_lubTheory llistTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem challenge_machine_sem_total:
   ∃b. challengeMachineSem mc st ms b
Proof
  Cases_on`∃k t. FST (challengeEvaluate mc st k ms) = Halt t`
  >- (
    fs[]
    \\ qexists_tac`Terminate t (SND(SND(challengeEvaluate mc st k ms))).io_events`
    \\ simp[challengeMachineSem_def]
    \\ Cases_on`challengeEvaluate mc st k ms`
    \\ qexists_tac`k` \\ fs[]
    \\ Cases_on`r` \\ fs[] )
  \\ Cases_on`∃k. FST (challengeEvaluate mc st k ms) = Error`
  >- ( qexists_tac`Fail` \\ simp[challengeMachineSem_def] )
  \\ qexists_tac`Diverge (lprefix_lub$build_lprefix_lub (IMAGE (λk. fromList (SND(SND(challengeEvaluate mc st k ms))).io_events) UNIV))`
  \\ simp[challengeMachineSem_def]
  \\ conj_tac
  >- (
    rw[]
    \\ Cases_on`challengeEvaluate mc st k ms`
    \\ fs[GSYM EXISTS_PROD]
    \\ metis_tac[targetSemTheory.machine_result_nchotomy, FST] )
  \\ irule build_lprefix_lub_thm
  \\ simp[IMAGE_COMPOSE, GSYM o_DEF]
  \\ irule prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def, PULL_EXISTS]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ metis_tac[LESS_EQ_CASES,challenge_add_clock_io_events_mono]
QED


Theorem challenge_singleton_termination:
  challengeMachineSem mc st ms SUBSET {Terminate result events} ==>
  ?k ms' st'. challengeEvaluate mc st k ms = (Halt result,ms',st') /\
    st'.io_events = events
Proof
  strip_tac >>
  `challengeMachineSem mc st ms (Terminate result events)` by
    metis_tac [challenge_machine_sem_total,SUBSET_DEF,IN_DEF,IN_SING] >>
  fs [challengeMachineSem_def] >> metis_tac []
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "challenge totality assumptions")
  [challenge_machine_sem_total,challenge_singleton_termination];
