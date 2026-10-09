(* Observable native semantics of the fixed no-install challenge evaluator.
   Adapted from pinned CakeML lab_to_targetProof; see ../CAKEML-LICENSE. *)
Theory initChallengeSemantics
Ancestors initChallengeCompile initChallengeClock
Libs preamble BasicProvers
open ffiTheory labSemTheory labPropsTheory lab_to_targetTheory
  targetSemTheory targetPropsTheory lab_to_targetProofTheory
  initMachineTheory initChallengeCompileTheory initChallengeClockTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val s1 = ``s1:(64,lab_to_target$config,'ffi) labSem$state``;
Definition challengeMachineSem_def:
  (challengeMachineSem mc st ms (Terminate t io_list) <=>
     ?k ms' st'.
       challengeEvaluate mc st k ms = (Halt t,ms',st') ∧
       st'.io_events = io_list) /\
  (challengeMachineSem mc st ms (Diverge io_trace) <=>
     (!k. ?ms' st'. challengeEvaluate mc st k ms = (TimeOut,ms',st')) /\
     lprefix_lub
       (IMAGE
         (\k. fromList (SND (SND (challengeEvaluate mc st k ms))).io_events) UNIV)
       io_trace) /\
  (challengeMachineSem mc st ms Fail <=>
     ?k. FST (challengeEvaluate mc st k ms) = Error)
End

Theorem challenge_compile_correct_from_state:
  !^s1 res (mc_conf:(64,riscv_state,'b) machine_config) s2 code2 labs t1 ms1.
    oracle_tie mc_conf ms1 s1 /\
    labSem$evaluate s1 = (res,s2) /\ res <> Error /\
    encoder_correct mc_conf.target /\
    state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\ no_install s1.code ==>
    ?k ms2. challengeEvaluate mc_conf s1.ffi (s1.clock+k) ms1 = (res,ms2,s2.ffi)
Proof
  metis_tac [challenge_compile_correct]
QED

Theorem challenge_machine_sem_EQ_sem:
   !(mc_conf:(64,riscv_state,'b) machine_config) p (ms:riscv_state) ^s1.
     encoder_correct mc_conf.target /\
     init_ok (mc_conf,p) s1 ms /\ no_install s1.code /\ semantics s1 <> Fail ==>
     challengeMachineSem mc_conf s1.ffi ms = { semantics s1 }
Proof
  simp[GSYM AND_IMP_INTRO] >>
  rpt gen_tac >> ntac 3 strip_tac >>
  full_simp_tac(srw_ss())[init_ok_def] >>
  simp[semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >>
  conj_tac
  >- (
    (
      qx_gen_tac`ffi`>>strip_tac>> full_simp_tac(srw_ss())[]
      \\ imp_res_tac oracle_tie_clock
      \\ pop_assum (qspec_then `k` assume_tac)
      \\ old_drule challenge_compile_correct_from_state \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac state_rel_clock
      \\ pop_assum (qspec_then `k` assume_tac)
      \\ disch_then old_drule \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[challengeMachineSem_def,EXTENSION] \\ full_simp_tac(srw_ss())[IN_DEF]
      \\ Cases \\ full_simp_tac(srw_ss())[challengeMachineSem_def]
      THEN1 (disj1_tac \\ qexists_tac `k+k'` \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
      THEN1
       (eq_tac THEN1
         (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
          \\ old_drule (GEN_ALL challenge_ignore_clocks) \\ full_simp_tac(srw_ss())[]
          \\ pop_assum (K all_tac)
          \\ disch_then old_drule \\ full_simp_tac(srw_ss())[])
        \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
      \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[FST_EQ_EQUIV]
      \\ PairCases_on `y`
      \\ old_drule (GEN_ALL challenge_ignore_clocks) \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ pop_assum (K all_tac)
      \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
  )
  \\ full_simp_tac(srw_ss())[challengeMachineSem_def,EXTENSION] \\ full_simp_tac(srw_ss())[IN_DEF]
  \\ strip_tac
  \\ Cases \\ full_simp_tac(srw_ss())[challengeMachineSem_def]
  \\ imp_res_tac state_rel_clock
  >- (
    (
      qmatch_abbrev_tac`a ∧ b ⇔ c` >>
      sg `a`
      >- (
        (
          unabbrev_all_tac >> gen_tac >>
          `oracle_tie mc_conf ms (s1 with clock := k)` by
            (irule oracle_tie_clock \\ first_assum ACCEPT_TAC) >>
          qspec_then `s1 with clock := k` mp_tac challenge_compile_correct_from_state >>
          Cases_on`labSem$evaluate (s1 with clock := k)`>>simp[]>>
          last_assum(qspec_then`k`mp_tac)>>
          pop_assum mp_tac >> simp_tac(srw_ss())[] >>
          ntac 2 strip_tac >>
          disch_then old_drule >>
          disch_then old_drule >>
          first_x_assum(qspec_then`k`strip_assume_tac) >>
          disch_then old_drule >> strip_tac >>
          first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
          strip_tac >>
          spose_not_then strip_assume_tac >>
          Cases_on`q`>>full_simp_tac(srw_ss())[]>>
          `∃x y z. challengeEvaluate mc_conf s1.ffi k ms = (x,y,z)` by metis_tac[PAIR] >>
          `x = TimeOut` by (
            spose_not_then strip_assume_tac >>
            old_drule (GEN_ALL challenge_add_clock) >>
            simp[] >> qexists_tac`k'`>>simp[] ) >>
          full_simp_tac(srw_ss())[] >>
          metis_tac[challenge_add_clock_io_events_mono,SND,option_CASES,
                    IS_SOME_EXISTS,LESS_EQ_EXISTS])
      )
      >- (
        simp[] >> full_simp_tac(srw_ss())[Abbr`a`] >>
        unabbrev_all_tac >> simp[] >>
        qmatch_abbrev_tac`lprefix_lub l1 l ⇔ l = build_lprefix_lub l2` >>
        `lprefix_chain l1 ∧ lprefix_chain l2` by (
          unabbrev_all_tac >>
          conj_tac >>
          Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
          REWRITE_TAC[IMAGE_COMPOSE] >>
          match_mp_tac prefix_chain_lprefix_chain >>
          simp[prefix_chain_def,PULL_EXISTS] >>
          qx_genl_tac[`k1`,`k2`] >>
          qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
          metis_tac[
            challenge_add_clock_io_events_mono,
            labPropsTheory.evaluate_add_clock_io_events_mono
            |> Q.SPEC`s with clock := k` |> SIMP_RULE (srw_ss())[],
            LESS_EQ_EXISTS]) >>
        `equiv_lprefix_chain l1 l2` by (
          simp[equiv_lprefix_chain_thm] >>
          unabbrev_all_tac >> simp[PULL_EXISTS] >>
          ntac 2 (pop_assum kall_tac) >>
          simp[LNTH_fromList,PULL_EXISTS] >>
          simp[GSYM FORALL_AND_THM] >>
          rpt gen_tac >>
          `oracle_tie mc_conf ms (s1 with clock := k)` by
            (irule oracle_tie_clock \\ first_assum ACCEPT_TAC) >>
          qspec_then `s1 with clock := k` mp_tac challenge_compile_correct_from_state >>
          Cases_on`labSem$evaluate (s1 with clock := k)`>>full_simp_tac(srw_ss())[] >>
          last_assum(qspec_then`k`mp_tac)>>
          pop_assum mp_tac >> simp_tac(srw_ss())[] >>
          ntac 2 strip_tac >>
          disch_then old_drule >>
          disch_then old_drule >>
          first_x_assum(qspec_then`k`(fn th => assume_tac th >> disch_then old_drule)) >>
          strip_tac >>
          reverse conj_tac >> strip_tac >- (
            qexists_tac`k+k'`>>simp[] ) >>
          qmatch_assum_abbrev_tac`n < (LENGTH (_ ffi))` >>
          qexists_tac`k`>>simp[] >>
          `ffi.io_events ≼ r.ffi.io_events` by (
            qunabbrev_tac`ffi` >>
            metis_tac[
              challenge_add_clock_io_events_mono,
              SND,LESS_EQ_EXISTS] ) >>
          full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
          simp[EL_APPEND1]) >>
        metis_tac[build_lprefix_lub_thm,unique_lprefix_lub,lprefix_lub_new_chain]
      ))
  )
  >- (
    (
      spose_not_then strip_assume_tac >> var_eq_tac >>
      `oracle_tie mc_conf ms (s1 with clock := k)` by
        (irule oracle_tie_clock \\ first_assum ACCEPT_TAC) >>
      qspec_then `s1 with clock := k` mp_tac challenge_compile_correct_from_state >>
      Cases_on`labSem$evaluate (s1 with clock := k)`>>simp[]>>
      last_assum(qspec_then`k`mp_tac)>>
      pop_assum mp_tac >> simp_tac(srw_ss())[] >> rpt strip_tac >>
      asm_exists_tac >> simp[] >>
      first_x_assum(qspec_then`k`strip_assume_tac) >>
      asm_exists_tac >> simp[] >>
      rpt gen_tac >>
      old_drule (GEN_ALL challenge_add_clock) >> simp[] >>
      disch_then kall_tac >>
      first_x_assum(qspec_then`k`mp_tac) >> simp[] >>
      metis_tac[])
  )
  >- (
    CCONTR_TAC \\ full_simp_tac(srw_ss())[FST_EQ_EQUIV]
    \\ last_x_assum (qspec_then `k` mp_tac) \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `labSem$evaluate (s1 with clock := k)` \\ full_simp_tac(srw_ss())[]
    \\ CCONTR_TAC
    \\ `oracle_tie mc_conf ms (s1 with clock := k)` by
         (irule oracle_tie_clock \\ first_assum ACCEPT_TAC)
    \\ old_drule challenge_compile_correct_from_state
    \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `code2` \\ qexists_tac `labs` \\ qexists_tac `t1`
    \\ conj_tac
    >- (
      qpat_x_assum `!k'. state_rel _ _ _ _` (qspec_then `k` assume_tac)
      \\ first_assum ACCEPT_TAC
    )
    \\ rpt gen_tac
    \\ PairCases_on `y`
    \\ old_drule (GEN_ALL challenge_add_clock) \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  )
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "challenge observable semantics assumptions")
  [challenge_compile_correct_from_state,challenge_machine_sem_EQ_sem];
