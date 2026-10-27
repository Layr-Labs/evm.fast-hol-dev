(* Clock and observation properties of the fixed challenge evaluator.
   Adapted from pinned CakeML targetProps; see ../CAKEML-LICENSE. *)
Theory initChallengeClock
Ancestors initMachine targetProps
Libs preamble
open ffiTheory targetSemTheory targetPropsTheory initMachineTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem challenge_add_clock:
   ∀mc_conf ffi k ms k1 r ms1 st1.
    challengeEvaluate mc_conf ffi k ms = (r,ms1,st1) /\ r <> TimeOut ==>
    challengeEvaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)
Proof
  ho_match_mp_tac challengeEvaluate_ind >> srw_tac[][] >>
  qhdtm_x_assum`challengeEvaluate` mp_tac >>
  simp[Once challengeEvaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  simp[Once challengeEvaluate_def,SimpR``$==>``] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[apply_oracle_def] >- (
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`k1`mp_tac) >> simp[] ) >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> fs[] \\
  rpt (TOP_CASE_TAC \\ fs[])
QED

Theorem challenge_io_events_mono:
   ∀mc_conf ffi k ms.
     ffi.io_events ≼ (SND(SND(challengeEvaluate mc_conf ffi k ms))).io_events
Proof
  ho_match_mp_tac challengeEvaluate_ind >>
  rpt gen_tac >> strip_tac >> once_rewrite_tac [challengeEvaluate_def] >>
  rpt (TOP_CASE_TAC >> fs [apply_oracle_def]) >>
  gvs [call_FFI_def,bool_case_eq] >> rpt (FULL_CASE_TAC >> gvs []) >>
  irule IS_PREFIX_TRANS >> first_assum (irule_at Any) >> fs [IS_PREFIX_APPEND]
QED

Theorem challenge_add_clock_io_events_mono:
   ∀mc_conf ffi k ms k'.
   k ≤ k' ⇒
   (SND(SND(challengeEvaluate mc_conf ffi k ms))).io_events ≼
   (SND(SND(challengeEvaluate mc_conf ffi k' ms))).io_events
Proof
  ho_match_mp_tac challengeEvaluate_ind >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp_tac(srw_ss())[Once challengeEvaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >- METIS_TAC[challenge_io_events_mono] >>
  `k <= k' + 1` by decide_tac >>
  rpt (TOP_CASE_TAC >> fs[apply_oracle_def]) >>
  res_tac >>
  CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once challengeEvaluate_def])) >>
  fs [apply_oracle_def]
  >- (
    TOP_CASE_TAC >> fs[] >>
    METIS_TAC[challenge_io_events_mono]
  ) >>
  namedCases_on `mc_conf.mmio_info x` ["r0 r1 r2 r3"] >>
  gvs[] >>
  rpt (TOP_CASE_TAC >> fs[])
QED

Theorem challenge_ignore_clocks:
  challengeEvaluate mc ffi k ms = (r1,ms1,st1) /\ r1 <> TimeOut /\
  challengeEvaluate mc ffi k' ms = (r2,ms2,st2) /\ r2 <> TimeOut ==>
  (r1,ms1,st1) = (r2,ms2,st2)
Proof
  rw [] >> imp_res_tac challenge_add_clock >>
  pop_assum (qspec_then `k'` mp_tac) >>
  pop_assum (qspec_then `k` mp_tac) >>
  fs [AC ADD_ASSOC ADD_COMM]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "challenge clock assumptions")
  [challenge_add_clock,challenge_io_events_mono,
   challenge_add_clock_io_events_mono,challenge_ignore_clocks];
