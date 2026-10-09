(* Padding-aware simulation in the fixed challenge evaluator.
   Adapted from pinned CakeML lab_to_targetProof; see ../CAKEML-LICENSE. *)
Theory initChallengeNop
Ancestors initChallengeStep
Libs preamble wordsLib
open asmTheory asmSemTheory asmPropsTheory targetSemTheory targetPropsTheory
  lab_to_targetProofTheory initMachineTheory initChallengeStepTheory wordsTheory
  miscTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem enc_with_nop_thm[local]:
  enc_with_nop enc (b:asm) bytes =
      ?n. bytes = enc b ++ FLAT (REPLICATE n (enc (asm$Inst Skip)))
Proof
  fs [enc_with_nop_def,LENGTH_NIL]
  \\ IF_CASES_TAC \\ fs [FLAT_REPLICATE_NIL]
  \\ EQ_TAC \\ rw [] THEN1 metis_tac []
  \\ fs [LENGTH_APPEND,LENGTH_FLAT,map_replicate,SUM_REPLICATE]
  \\ full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL,MULT_DIV]
QED

val challenge_nop_step =
  asm_step_IMP_challenge_step
    |> SIMP_RULE std_ss [asm_step_def]
    |> SPEC_ALL |> Q.INST [`i`|->`Inst Skip`]
    |> SIMP_RULE (srw_ss()) [asm_def,inst_def,asm_ok_def,inst_ok_def,
         Once upd_pc_def,GSYM CONJ_ASSOC]

Theorem shift_interfer_0[local]:
  shift_interfer 0 = I
Proof
  full_simp_tac(srw_ss())[shift_interfer_def,FUN_EQ_THM,shift_seq_def,
      machine_config_component_equality]
QED

Theorem upd_pc_with_pc[local]:
  upd_pc s1.pc s1 = s1:64 asm_state
Proof
  full_simp_tac(srw_ss())[asm_state_component_equality,upd_pc_def]
QED

Theorem shift_interfer_twice[simp]:
   shift_interfer l' (shift_interfer l c) =
    shift_interfer (l + l') c
Proof
  full_simp_tac(srw_ss())[shift_interfer_def,shift_seq_def,AC ADD_COMM ADD_ASSOC]
QED

Theorem challenge_nop_steps[local]:
  !n s1 ms1 (c:(64,riscv_state,'c)machine_config).
      encoder_correct c.target /\
      c.prog_addresses = s1.mem_domain /\
      ffi_entry_pcs_disjoint c s1
        (n * LENGTH (c.target.config.encode (Inst Skip))) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      bytes_in_memory s1.pc
        (FLAT (REPLICATE n (c.target.config.encode (Inst Skip)))) s1.mem
        s1.mem_domain /\
      (case c.target.config.link_reg of NONE => T | SOME r => s1.lr = r) /\
      (s1.be <=> c.target.config.big_endian) /\
      s1.align = c.target.config.code_alignment /\ ~s1.failed /\
      target_state_rel c.target (s1:64 asm_state) (ms1:riscv_state) ==>
      ?l ms2.
        !k.
          (challengeEvaluate c io (k + l) ms1 =
           challengeEvaluate (shift_interfer l c) io k ms2) /\
          (find_next_interference c io (k + l) ms1 =
           find_next_interference (shift_interfer l c) io k ms2) /\
          target_state_rel c.target
            (upd_pc
              (s1.pc +
               n2w (n * LENGTH (c.target.config.encode (Inst Skip)))) s1)
            ms2
Proof
  Induct \\ full_simp_tac(srw_ss())[] THEN1
   (rpt strip_tac \\ Q.LIST_EXISTS_TAC [`0`,`ms1`]
    \\ full_simp_tac(srw_ss())[shift_interfer_0,upd_pc_with_pc])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[REPLICATE,bytes_in_memory_APPEND]
  \\ mp_tac challenge_nop_step \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ pop_assum mp_tac
  \\ impl_tac
  >- (
    fs[ffi_entry_pcs_disjoint_def,IN_DISJOINT,DISJOINT_SUBSET]
    \\ rw[]
    \\ last_x_assum $ qspec_then `x` assume_tac
    \\ fs[addressTheory.word_arith_lemma1,MULT_SUC]
    \\ disj2_tac
    \\ strip_tac
    \\ first_x_assum $ qspec_then `a` assume_tac
    \\ disch_then assume_tac
    \\ first_x_assum $ drule_then assume_tac
    \\ rw[]
  )
  \\ strip_tac
  \\ first_x_assum (mp_tac o
       Q.SPECL [`(upd_pc (s1.pc +
          n2w (LENGTH ((c:(64,riscv_state,'c) machine_config).target.config.encode
            (Inst Skip)))) s1)`,`ms2`,`shift_interfer l (c:(64,riscv_state,'c)machine_config)`])
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (
    fs[shift_interfer_def,upd_pc_def,interference_ok_def,shift_seq_def,
      ffi_entry_pcs_disjoint_def,IN_DISJOINT,DISJOINT_SUBSET]
    \\ strip_tac
    \\ last_x_assum $ qspec_then `x` assume_tac
    \\ fs[addressTheory.word_arith_lemma1,MULT_SUC]
    \\ disj2_tac
    \\ strip_tac
    \\ first_x_assum $ qspec_then `a + LENGTH ((c:(64,riscv_state,'c)machine_config).target.config.encode (Inst Skip))` assume_tac
    \\ disch_then assume_tac
    \\ first_x_assum $ drule_then assume_tac
    \\ rw[]
  )
  \\ rpt strip_tac
  \\ `(shift_interfer l (c:(64,riscv_state,'c)machine_config)).target = (c:(64,riscv_state,'c)machine_config).target` by full_simp_tac(srw_ss())[shift_interfer_def]
  \\ full_simp_tac(srw_ss())[upd_pc_def]
  \\ Q.LIST_EXISTS_TAC [`l'+l`,`ms2'`]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,
       word_add_n2w,AC ADD_COMM ADD_ASSOC,MULT_CLAUSES]
  \\ full_simp_tac(srw_ss())[ADD_ASSOC] \\ rpt strip_tac
  \\ first_x_assum (mp_tac o Q.SPEC `k`)
  \\ first_x_assum (mp_tac o Q.SPEC `k+l'`)
  \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
  \\ gvs [word_add_n2w]
QED

Theorem asm_step_IMP_challenge_step_nop:
   !(c:(64,riscv_state,'c)machine_config) s1 ms1 io i s2 bytes.
      encoder_correct c.target /\
      c.prog_addresses = s1.mem_domain /\
      ffi_entry_pcs_disjoint c s1 (LENGTH bytes) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      bytes_in_memory s1.pc bytes s2.mem s1.mem_domain /\
      asm_step_nop bytes c.target.config s1 i s2 /\
      s2 = asm i (s1.pc + n2w (LENGTH bytes)) s1 /\
      target_state_rel c.target (s1:64 asm_state) (ms1:riscv_state) /\
      (!x. i <> Call x) ==>
      ?l ms2.
        !k.
          (challengeEvaluate c io (k + l) ms1 =
           challengeEvaluate (shift_interfer l c) io k ms2) /\
          (find_next_interference c io (k + l) ms1 =
           find_next_interference (shift_interfer l c) io k ms2) /\
          target_state_rel c.target s2 ms2 /\ l <> 0
Proof
  full_simp_tac(srw_ss())[asm_step_nop_def] \\ rpt strip_tac
  \\ (asm_step_IMP_challenge_step
      |> SIMP_RULE std_ss [asm_step_def] |> SPEC_ALL |> mp_tac) \\ fs[]
  \\ full_simp_tac(srw_ss())[enc_with_nop_thm]
  \\ match_mp_tac IMP_IMP \\ strip_tac THEN1
   (conj_tac
    >- (
      fs[LENGTH_APPEND]
      \\ old_drule ffi_entry_pcs_disjoint_LENGTH_shorter
      \\ disch_then $ qspec_then `LENGTH ((c:(64,riscv_state,'c)machine_config).target.config.encode i)` assume_tac
      \\ fs[])
    \\ fs[bytes_in_memory_APPEND]
    \\ Cases_on `i`
    \\ fs[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def,LET_DEF,assert_def]
    \\ srw_tac[][] \\ fs[] \\ rfs[])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ Cases_on `?w. i = Jump w` \\ full_simp_tac(srw_ss())[]
  THEN1 (
    full_simp_tac(srw_ss())[asm_def]
    \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
    \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `?cmp n r w. (i = JumpCmp cmp n r w) /\
                  word_cmp cmp (read_reg n s1) (reg_imm r s1)` \\ fs[]
  THEN1 (
    srw_tac[][]
    \\ full_simp_tac(srw_ss())[asm_def]
    \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
    \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `?r. (i = JumpReg r)` \\ fs[]
  THEN1 (
    srw_tac[][]
    \\ full_simp_tac(srw_ss())[asm_def,LET_DEF]
    \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
    \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[])
  \\ qspecl_then
      [`n`,`asm i (s1.pc + n2w (LENGTH ((c:(64,riscv_state,'c)machine_config).target.config.encode i))) s1`,`ms2`,
       `shift_interfer l (c:(64,riscv_state,'c)machine_config)`] mp_tac challenge_nop_steps
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[shift_interfer_def] \\ rpt strip_tac
    THEN1 (
      fs[ffi_entry_pcs_disjoint_def,IN_DISJOINT]
      \\ Cases_on `i`
      \\ fs[asm_def]
      \\ rw[]
      \\ first_x_assum $ qspec_then `x` assume_tac
      \\ fs[addressTheory.word_arith_lemma1]
      \\ disj2_tac
      \\ ntac 2 strip_tac
      \\ first_x_assum old_drule
      \\ gvs[]
    )
    THEN1 (fs[interference_ok_def,shift_seq_def])
    THEN1
     (Q.ABBREV_TAC
        `mm = (asm i (s1.pc + n2w (LENGTH ((c:(64,riscv_state,'c)machine_config).target.config.encode i))) s1).mem`
      \\ full_simp_tac(srw_ss())[Once (asm_mem_ignore_new_pc |> Q.SPECL [`i`,`0w`])]
      \\ `!w. (asm i w s1).pc = w` by (Cases_on `i` \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def])
      \\ full_simp_tac(srw_ss())[bytes_in_memory_APPEND])
    \\ metis_tac [asm_failed_ignore_new_pc])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ Q.LIST_EXISTS_TAC [`l+l'`,`ms2'`]
  \\ full_simp_tac(srw_ss())[PULL_FORALL] \\ strip_tac
  \\ qpat_x_assum `!k. challengeEvaluate _ io _ ms2 = _ /\ _` (mp_tac o Q.SPEC `k:num`)
  \\ qpat_x_assum `!k. challengeEvaluate _ io _ ms1 = _ /\ _` (mp_tac o Q.SPEC `k+l':num`)
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
  \\ full_simp_tac(srw_ss())[shift_interfer_def]
  \\ qpat_x_assum `target_state_rel (c:(64,riscv_state,'c)machine_config).target xx yy` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x = z) ==> (f x y ==> f z y)``)
  \\ Cases_on `i` \\ full_simp_tac(srw_ss())[asm_def]
  \\ full_simp_tac(srw_ss())[LENGTH_FLAT,SUM_REPLICATE,map_replicate]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ fs [GSYM word_add_n2w]
  THEN1 (Cases_on `i'` \\ full_simp_tac(srw_ss())[inst_def,upd_pc_def]
    \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w])
  \\ full_simp_tac(srw_ss())[jump_to_offset_def,upd_pc_def]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
QED


val _ = if null(hyp asm_step_IMP_challenge_step_nop)
  then ignore(check_thm asm_step_IMP_challenge_step_nop)
  else failwith "padded challenge step assumptions";
