(* Adapted from the pinned CakeML targetProps normal-instruction proof.
   See ../CAKEML-LICENSE. The prefix stays inside program addresses outside
   FFI entries, so only the normal-instruction branch of the fixed challenge
   evaluator is unfolded; cache-hook and FFI behavior are not changed. *)
Theory initChallengeStep
Ancestors initMachine targetProps lab_to_targetProof
Libs preamble wordsLib
open asmTheory asmSemTheory asmPropsTheory targetSemTheory targetPropsTheory
  miscTheory initMachineTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem shift_interfer_intro[local]:
  shift_interfer k1 (shift_interfer k2 c) = shift_interfer (k1+k2) c
Proof
  metis_tac [lab_to_targetProofTheory.shift_interfer_twice,ADD_COMM]
QED
fun stage name : tactic = fn g => (print (name ^ "\n"); ALL_TAC g);
Theorem challenge_EQ_challenge_lemma:
  !n ms1 (c:(64,riscv_state,'c) machine_config).
      c.target.get_pc ms1 IN (c.prog_addresses DIFF (set c.ffi_entry_pcs)) /\
      c.target.state_ok ms1 /\
      (c.prog_addresses = dm) ∧
      interference_ok c.next_interfer (c.target.proj dm) /\
      (!s ms. target_state_rel c.target s ms ==> c.target.state_ok ms) /\
      (!ms1 ms2. (c.target.proj dm ms1 = c.target.proj dm ms2) ==>
           (c.target.state_ok ms1 = c.target.state_ok ms2) /\
           (c.target.get_pc ms1 = c.target.get_pc ms2) /\
           (∀a. a ∈ dm ⇒ c.target.get_byte ms1 a = c.target.get_byte ms2 a)) /\
      (!env.
         interference_ok env (c.target.proj dm) ==>
         asserts n (\k s. env k (c.target.next s)) ms1
           (\ms'. c.target.state_ok ms' /\
                  (∀pc. pc ∈ all_pcs (LENGTH (c.target.config.encode i)) init_pc 0 ⇒
                   c.target.get_byte ms' pc = c.target.get_byte ms1 pc) /\
                  c.target.get_pc ms' ∈
                    all_pcs (LENGTH (c.target.config.encode i)) init_pc c.target.config.code_alignment)
           (\ms'. target_state_rel c.target s2 ms')) /\
      (asserts2 (n + 1) (λk. c.next_interfer (n + 1 - k)) c.target.next ms1
        (λms1 ms2. ∀x. x ∉ dm ⇒ c.target.get_byte ms1 x = c.target.get_byte ms2 x)) ∧
      (∃k.
        c.target.get_pc ms1 = init_pc + n2w (k * (2 ** c.target.config.code_alignment)) /\
        k * (2 ** c.target.config.code_alignment) < LENGTH (c.target.config.encode i) /\
        bytes_in_memory init_pc (c.target.config.encode i)
          (c.target.get_byte ms1) (c.prog_addresses DIFF set c.ffi_entry_pcs)) ==>
      ?ms2.
        !k. (challengeEvaluate c io (k + (n + 1)) ms1 =
             challengeEvaluate (shift_interfer (n+1) c) io k ms2) /\
            (find_next_interference c io (k + (n + 1)) ms1 =
             find_next_interference (shift_interfer (n+1) c) io k ms2) /\
            target_state_rel c.target s2 ms2
Proof
  Induct THEN1
   (stage "challenge base" \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ stage "base asserts" \\ full_simp_tac(srw_ss())[asserts_def,LET_DEF]
    \\ stage "unfold evaluator" \\ SIMP_TAC std_ss [Once challengeEvaluate_def, Once find_next_interference_def]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ stage "base interference" \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `K ((c:(64,riscv_state,'c) machine_config).next_interfer 0)`)
    \\ full_simp_tac(srw_ss())[interference_ok_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ stage "base result" \\ REPEAT STRIP_TAC \\ RES_TAC \\ simp_tac std_ss [shift_interfer_def,apply_oracle_def]
    \\ reverse TOP_CASE_TAC
    >- (
      `F` suffices_by fs[]
      \\ pop_assum mp_tac
      \\ fs[encoded_bytes_in_mem_def]
      \\ asm_exists_tac
      \\ qmatch_goalsub_abbrev_tac`DROP m ls`
      \\ qmatch_goalsub_abbrev_tac`bytes_in_memory _ _ mm dm`
      \\ Q.ISPECL_THEN[`TAKE m ls`,`DROP m ls`,`init_pc`,`mm`,`dm`]mp_tac bytes_in_memory_APPEND
      \\ rfs[]
      \\ metis_tac[DIFF_SUBSET,bytes_in_memory_SUBSET])
    \\ reverse TOP_CASE_TAC
    >- (
      `F` suffices_by fs[]
      \\ pop_assum mp_tac
      \\ fs[Once asserts2_def]
      \\ metis_tac[] )
    \\ metis_tac [])
  \\ stage "challenge induction" \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD_CLAUSES]
  \\ stage "unfold evaluator" \\ SIMP_TAC std_ss [Once challengeEvaluate_def, Once find_next_interference_def]
  \\ full_simp_tac(srw_ss())[ADD1] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Q.PAT_ASSUM `!i. bbb`(qspec_then`λi. (c:(64,riscv_state,'c) machine_config).next_interfer 0`mp_tac)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def])
  \\ full_simp_tac(srw_ss())[]
  \\ SIMP_TAC bool_ss [GSYM ADD1,asserts_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ strip_tac
  \\ `(c:(64,riscv_state,'c) machine_config).target.state_ok ((c:(64,riscv_state,'c) machine_config).target.next ms1)` by metis_tac [interference_ok_def]
  \\ full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `!ms1 (c:(64,riscv_state,'c) machine_config). bbb ==> ?x. bb`
        (MP_TAC o Q.SPECL [`((c:(64,riscv_state,'c) machine_config).next_interfer 0 ((c:(64,riscv_state,'c) machine_config).target.next ms1))`,
                    `((c:(64,riscv_state,'c) machine_config) with next_interfer := shift_seq 1 (c:(64,riscv_state,'c) machine_config).next_interfer)`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[]
    \\ conj_tac >- (
      fs[all_pcs_thm,SUBSET_DEF,PULL_EXISTS]
      \\ first_assum(mp_then Any mp_tac (GEN_ALL bytes_in_memory_all_pcs))
      \\ fs[SUBSET_DEF]
      \\ disch_then match_mp_tac
      \\ simp[all_pcs_thm]
      \\ metis_tac[])
    \\ conj_tac THEN1 (full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def])
    \\ conj_tac THEN1 (rpt strip_tac \\ RES_TAC)
    \\ conj_tac >- (
      rpt strip_tac
      \\ FIRST_ASSUM (MP_TAC o Q.SPEC
           `\k. if k = SUC n then (c:(64,riscv_state,'c) machine_config).next_interfer 0 else env k`) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP
      \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def] \\ srw_tac[][])
      \\ simp[GSYM ADD1, asserts_def]
      \\ MATCH_MP_TAC asserts_WEAKEN
      \\ simp_tac(srw_ss())[FUN_EQ_THM]
      \\ rw[])
    \\ conj_tac >-  (
      qhdtm_x_assum`asserts2`mp_tac
      \\ simp[Once asserts2_def, shift_seq_def]
      \\ rw[]
      \\ irule asserts2_change_interfer
      \\ simp[]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[] )
    \\ `(c:(64,riscv_state,'c) machine_config).target.proj dm ((c:(64,riscv_state,'c) machine_config).next_interfer 0 ((c:(64,riscv_state,'c) machine_config).target.next ms1)) =
        (c:(64,riscv_state,'c) machine_config).target.proj dm ((c:(64,riscv_state,'c) machine_config).target.next ms1)` by fs[interference_ok_def]
    \\ qpat_x_assum`∀ms1 ms2. _ ⇒ _` drule
    \\ strip_tac \\ fs[]
    \\ rfs[all_pcs_thm]
    \\ qmatch_asmsub_rename_tac`x * _ < _`
    \\ qexists_tac`x` \\ simp[]
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ qx_gen_tac`j` \\ strip_tac
    \\ first_x_assum(qspec_then`init_pc + n2w j`mp_tac)
    \\ impl_tac
    >- (
      imp_res_tac bytes_in_memory_all_pcs
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ fs[all_pcs_thm,SUBSET_DEF,PULL_EXISTS] )
    \\ rw[]
    \\ first_x_assum(qspec_then`λi x. x`mp_tac)
    \\ impl_tac >- fs[interference_ok_def]
    \\ strip_tac
    \\ drule asserts_IMP_FOLDR_COUNT_LIST_LESS
    \\ disch_then(qspec_then`0`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[]
    \\ strip_tac
    \\ first_x_assum (match_mp_tac o GSYM)
    \\ qexists_tac`j`
    \\ simp[] )
  \\ strip_tac \\ fs[]
  \\ qexists_tac`ms2`
  \\ reverse TOP_CASE_TAC
  >- (
    `F` suffices_by fs[]
    \\ pop_assum mp_tac
    \\ simp[encoded_bytes_in_mem_def]
    \\ qexists_tac`i`
    \\ qmatch_assum_abbrev_tac`k * a < LENGTH bs`
    \\ Q.ISPECL_THEN[`TAKE (k * a) bs`,`DROP (k * a) bs`,`init_pc`]mp_tac bytes_in_memory_APPEND
    \\ simp[]
    \\ metis_tac[MULT_COMM,bytes_in_memory_SUBSET,DIFF_SUBSET] )
  \\ rw[]
  \\ fs[GSYM shift_interfer_def, shift_interfer_intro,apply_oracle_def]
  \\ fs[GSYM ADD1]
  \\ simp[ADD1]
  \\ TOP_CASE_TAC
  \\ `F` suffices_by fs[]
  \\ pop_assum mp_tac \\ simp[]
  \\ imp_res_tac asserts2_first \\ fs[]
QED

Theorem enc_ok_not_empty[local]:
  enc_ok c /\ asm_ok w c ==> (c.encode w <> [])
Proof
  metis_tac [listTheory.LENGTH_NIL,enc_ok_def]
QED

Theorem asm_step_IMP_challenge_step:
  !(c:(64,riscv_state,'c) machine_config) s1 ms1 io i.
      encoder_correct c.target /\
      (c.prog_addresses = s1.mem_domain) /\
      ffi_entry_pcs_disjoint c s1 (LENGTH $ c.target.config.encode i) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      asm_step c.target.config s1 i
        (asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1) /\
      target_state_rel c.target (s1:64 asm_state) (ms1:riscv_state) ==>
      ?l ms2. !k. (challengeEvaluate c io (k + l) ms1 =
                   challengeEvaluate (shift_interfer l c) io k ms2) /\
                  (find_next_interference c io (k + l) ms1 =
                   find_next_interference (shift_interfer l c) io k ms2) /\
                  target_state_rel c.target
                    (asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1)
                    ms2 /\ l <> 0
Proof
  fs[encoder_correct_def,target_ok_def,LET_DEF,ffi_entry_pcs_disjoint_def]
  \\ rw[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ qexists_tac`n+1` \\ fs[]
  \\ MATCH_MP_TAC (GEN_ALL challenge_EQ_challenge_lemma)
  \\ qexists_tac`s1.pc`
  \\ qexists_tac`i`
  \\ Q.EXISTS_TAC `s1.mem_domain`
  \\ fs[]
  \\ conj_tac
  >- (
    fs[asm_step_def]
    \\ fs[target_state_rel_def]
    \\ imp_res_tac bytes_in_memory_all_pcs
    \\ fs[SUBSET_DEF,all_pcs_thm,PULL_EXISTS]
    \\ conj_tac >- (
      first_x_assum(qspec_then`1`mp_tac)
      \\ simp[]
      \\ disch_then(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then irule
      \\ Cases_on`(c:(64,riscv_state,'c) machine_config).target.config.encode i` \\ fs[]
      \\ pop_assum mp_tac \\ simp[]
      \\ match_mp_tac enc_ok_not_empty
      \\ fs[] )
    >- (
      fs[DISJOINT_DEF,INTER_DEF,EXTENSION,EMPTY_DEF]
      \\ qpat_x_assum `!x. ~(MEM x (c:(64,riscv_state,'c) machine_config).ffi_entry_pcs) \/ _` $ qspec_then `s1.pc`
        assume_tac
      \\ fs[]
      \\ first_x_assum $ qspec_then `0` assume_tac
      \\ gvs[]
      \\ drule enc_ok_not_empty
      \\ strip_tac
      \\ first_x_assum $ qspec_then `i` drule
      \\ fs[]
    ))
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- metis_tac[]
  \\ conj_tac >- (
    ntac 2 strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`\k. env (n - k)`])
    \\ simp[]
    \\ impl_tac
    >- fs[interference_ok_def]
    \\ disch_then(mp_tac o CONJUNCT1)
    \\ match_mp_tac asserts_WEAKEN
    \\ simp[] )
  \\ conj_tac >- (
    FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(c:(64,riscv_state,'c) machine_config).next_interfer`])
    \\ impl_tac >- fs[interference_ok_def]
    \\ disch_then(MATCH_ACCEPT_TAC o CONJUNCT2) )
  \\ qexists_tac`0`
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- (
    CCONTR_TAC \\ fs[]
    \\ pop_assum mp_tac
    \\ simp[]
    \\ match_mp_tac enc_ok_not_empty
    \\ fs[asm_step_def] )
  \\ fs[asm_step_def]
  \\ irule bytes_in_memory_change_mem
  \\ qexists `s1.mem`
  \\ conj_tac >- (
    fs[target_state_rel_def]
    \\ rw[]
    \\ first_x_assum (irule o GSYM)
    \\ drule (GEN_ALL bytes_in_memory_all_pcs)
    \\ simp[SUBSET_DEF, all_pcs_thm, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac) \\ simp[]
  )
  >- (
    irule bytes_in_memory_DIFF
    \\ qexistsl [`s1.mem_domain`, `set (c:(64,riscv_state,'c) machine_config).ffi_entry_pcs`]
    \\ gvs[]
  )
QED


val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "challenge instruction simulation assumptions")
  [challenge_EQ_challenge_lemma,asm_step_IMP_challenge_step];
