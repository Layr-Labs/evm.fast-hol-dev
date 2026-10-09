(* Compiler-level refinement for the fixed challenge evaluator.
   Adapted from pinned CakeML lab_to_targetProof; see ../CAKEML-LICENSE. *)
Theory initChallengeLabCompiler
Ancestors initChallengeSemantics initLabInitialState
Libs preamble BasicProvers wordsLib
open ffiTheory labSemTheory labPropsTheory labLangTheory lab_to_targetTheory
  lab_filterTheory lab_filterProofTheory asmTheory asmSemTheory asmPropsTheory
  targetSemTheory targetPropsTheory backendPropsTheory lab_to_targetProofTheory
  initLabInitialStateTheory initChallengeSemanticsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val IMP_LEMMA = METIS_PROVE [] ``(a ==> b) ==> (b ==> c) ==> (a ==> c)``;
Theorem challenge_semantics_make_init =
  challenge_machine_sem_EQ_sem |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> UNDISCH |> REWRITE_RULE []
  |> SIMP_RULE std_ss [init_ok_def,PULL_EXISTS,GSYM CONJ_ASSOC,GSYM AND_IMP_INTRO]
  |> SPEC_ALL |> Q.GEN `s1` |> Q.GEN `p`
  |> Q.GEN `t1` |> Q.SPEC `t`
  |> Q.SPEC `(mc_conf: (64,riscv_state,'b) machine_config).target.get_pc ms`
  |> Q.SPEC `make_init (mc_conf: (64,riscv_state,'b) machine_config)
       ffi t m dm sdm (ms:riscv_state) code
       (compile_lab mc_conf.target.config) (mc_conf.target.get_pc ms + (n2w (LENGTH (prog_to_bytes (code2:labLang$prog)))))
       cbspace coracle`
  |> SIMP_RULE std_ss [make_init_simp]
  |> MATCH_MP (MATCH_MP IMP_LEMMA IMP_state_rel_make_init)
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> REWRITE_RULE [oracle_tie_make_init]

Theorem all_enc_ok_pre_filter_skip[local]:
  ∀code c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (filter_skip code)
Proof
  Induct>>TRY(Cases)>>fs[lab_filterTheory.filter_skip_def]>>rw[]>>
  Induct_on`l`>>fs[]>>rw[]
QED

Theorem challenge_semantics_compile_lemma'[local]:
  mc_conf_ok (mc_conf:(64,riscv_state,'b) machine_config) ∧
  no_install code ∧
  (no_share_mem_inst code ==>
    compiler_oracle_ok coracle c'.labels (LENGTH bytes) (asm_conf:asm_config) mc_conf.ffi_names) ∧
  (* Assumptions on input code *)
  good_code mc_conf.target.config LN code ∧
  (* Config state *)
  asm_conf = mc_conf.target.config /\
  c.labels = LN ∧ c.pos = 0 ∧
  lab_to_target$compile asm_conf (c:lab_to_target$config) code = SOME (bytes,c') /\
  (* FFI is either given or computed *)
  c'.ffi_names = SOME mc_conf.ffi_names /\
  good_init_state mc_conf ms bytes cbspace t m dm sdm /\
  (* set up mmio_info and ffi_entry_pcs for mmio *)
  MAP (\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) c'.shmem_extra =
    DROP i (MAP w2n mc_conf.ffi_entry_pcs) /\
  mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH c'.shmem_extra),
                            (MAP (\rec. (rec.nbytes, Addr rec.addr_reg rec.addr_off,
                              rec.reg, n2w rec.exit_pc + mc_conf.target.get_pc ms))
                                 c'.shmem_extra)) /\
  no_install_or_no_share_mem code mc_conf.ffi_names /\
  (mmio_pcs_min_index mc_conf.ffi_names = SOME i) /\
  (* to avoid the ffi_entry_pc wraps around and overlaps with the program or code buffer *)
  cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:64) /\
  (* the original ffi names provided does not contain MappedRead or MappedWrite *)
  (!ffis. c.ffi_names = SOME ffis ==> EVERY (λx. ∃s. x = ExtCall s) ffis) /\
  semantics (make_init mc_conf ffi t m dm sdm ms code
    (lab_to_target$compile asm_conf) (mc_conf.target.get_pc ms+n2w(LENGTH bytes)) cbspace
    coracle
  ) <> Fail ==>
  challengeMachineSem mc_conf ffi ms =
  {semantics (make_init mc_conf ffi t m dm sdm ms code
    (lab_to_target$compile asm_conf) (mc_conf.target.get_pc ms+n2w(LENGTH bytes)) cbspace
    coracle
  )}
Proof
  fs[compile_def,compile_lab_def]>>
  pairarg_tac \\ fs[] \\
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  rw[]>>
  `compile mc_conf.target.config =
    (λc p. compile_lab mc_conf.target.config c (filter_skip p)) ` by
    fs[FUN_EQ_THM,compile_def]>>
  pop_assum SUBST_ALL_TAC>>
  gvs[] >>
  fs[GSYM make_init_filter_skip]>>
  SIMP_TAC (bool_ss) [Once WORD_ADD_COMM]>>
  qabbrev_tac `info=get_shmem_info q 0 [] []` >>
  first_x_assum $ mp_tac o GSYM o ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
  pairarg_tac >>
  strip_tac >>
  gvs[ELIM_UNCURRY] >>
  match_mp_tac (GEN_ALL $ SRULE[] challenge_semantics_make_init)>>
  fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip,no_install_filter_skip]>>
  fs[find_ffi_names_filter_skip,GSYM PULL_EXISTS,MAP_MAP_o,o_DEF]>>
  qpat_x_assum `_ ++ _ = mc_conf.ffi_names` $ assume_tac o GSYM >>
  conj_tac >- fs[mc_conf_ok_def] >>
  conj_tac >- (
    fs[good_code_def] >>
    fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip,no_install_filter_skip]>>
    fs[GSYM ALL_EL_MAP])>>
  rename1`_ = SOME (q,r)` >>
  qexists `r` >>
  fs[good_init_state_def] >>
  conj_tac >- (
    rpt strip_tac >>
    fs[compiler_oracle_ok_def,no_share_mem_filter_skip] >>
    rw[] >>
    rename1 `coracle k` >>
    last_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\ rw[] \\
    fs[good_code_def]>>
    fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip,no_install_filter_skip]>>
    fs[GSYM ALL_EL_MAP]
  )>>
  qmatch_asmsub_rename_tac `mmio_pcs_min_index (ffis ++ rest) = SOME i` >>
  `mmio_pcs_min_index (ffis ++ rest) = SOME (LENGTH ffis)` by (
    Cases_on`c.ffi_names`
    >- (
      gvs[] >>
      old_drule get_shmem_info_MappedRead_or_MappedWrite >>
      simp[Sh_not_Ext] >>
      strip_tac >>
      old_drule $ GEN_ALL mmio_pcs_min_index_APPEND_thm >>
      qmatch_assum_abbrev_tac`mmio_pcs_min_index (ffi' ++ _) = SOME _` >>
      disch_then $ qspec_then ‘ffi'’ mp_tac>>impl_tac >-
       (irule find_ffi_names_EVERY>>
        gvs[Abbr`ffi'`]>>metis_tac[])>>
      strip_tac>>fs[]
    ) >>
      gvs[] >>
      old_drule get_shmem_info_MappedRead_or_MappedWrite >>
      simp[Sh_not_Ext] >>
      strip_tac >>
      old_drule $ GEN_ALL mmio_pcs_min_index_APPEND_thm >>
      disch_then $ qspec_then ‘ffis’ mp_tac>>fs[]
  ) >>
  gvs[] >>
  conj_tac >- (
    gvs[TAKE_LENGTH_APPEND] >>
    Cases_on `c.ffi_names` >- (
      mp_tac find_ffi_names_EVERY>>
      disch_then $ qspec_then ‘code’ mp_tac>>
      simp[GSYM FILTER_EQ_ID]>>strip_tac>>fs[list_subset_refl])>>
    gvs[list_subset_TAKE,list_subset_refl]>>
    irule list_subset_trans>>
    last_assum $ irule_at Any>>
    mp_tac find_ffi_names_EVERY>>
    simp[GSYM FILTER_EQ_ID]>>
    strip_tac>>fs[list_subset_refl]
  ) >>
  conj_tac >- (
    qexists `c.init_clock` >>
    gvs[TAKE_LENGTH_APPEND]
  ) >>
  simp[DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
  simp[GSYM word_add_n2w, n2w_w2n]>>
  simp[no_install_or_no_share_mem_filter_skip] >>
  gvs[start_pc_ok_def,MEM_EL]>>
  rw[] >>
  spose_not_then assume_tac >>
  gvs[] >>
  last_x_assum $ drule_then assume_tac >>
  rw[]>>
  gvs[find_index_LEAST_EL] >>
  qpat_x_assum `(LEAST n'. _) = n` mp_tac >>
  DEEP_INTRO_TAC WhileTheory.LEAST_ELIM >>
  conj_tac
  >- (fs[MEM_EL] >> metis_tac[]) >>
  simp[] >>
  strip_tac >>
  spose_not_then kall_tac >>
  first_x_assum $ assume_tac o GSYM >>
  gvs[addressTheory.word_arith_lemma1,EL_TAKE] >>
  fs[ffi_offset_def] >>
  `16 * (n+3) < 18446744073709551616` by intLib.ARITH_TAC >>
  `0 < 16*(n+3) /\
   bn + LENGTH(prog_to_bytes q) + 16*(n+3) < 18446744073709551616 /\
   18446744073709551616 - 16*(n+3) < 18446744073709551616`
    by intLib.ARITH_TAC >>
  fs[] >> intLib.ARITH_TAC

QED

Theorem challenge_semantics_compile_lemma[local] =
  challenge_semantics_compile_lemma'
  |> REWRITE_RULE [CONJ_ASSOC]
  |> MATCH_MP implements_intro_gen
  |> REWRITE_RULE [GSYM CONJ_ASSOC];

Theorem challenge_semantics_compile:
  mc_conf_ok (mc_conf:(64,riscv_state,'b) machine_config) ∧
  no_install code ∧
  (no_share_mem_inst code ==>
    compiler_oracle_ok coracle c'.labels (LENGTH bytes) asm_conf mc_conf.ffi_names) ∧
  good_code asm_conf c.labels code ∧
  asm_conf = mc_conf.target.config ∧
  c.labels = LN ∧ c.pos = 0 ∧
  compile asm_conf c (code: sec list) = SOME (bytes,c') ∧
  c'.ffi_names = SOME mc_conf.ffi_names /\
  good_init_state mc_conf ms bytes cbspace t m dm sdm /\
  mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
  MAP (\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) c'.shmem_extra =
   DROP i (MAP w2n mc_conf.ffi_entry_pcs) /\
  mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH c'.shmem_extra),
                              (MAP (\rec. (rec.nbytes, Addr rec.addr_reg rec.addr_off,
                                rec.reg, n2w rec.exit_pc + mc_conf.target.get_pc ms))
                                   c'.shmem_extra)) /\
  no_install_or_no_share_mem code mc_conf.ffi_names /\
  (* to avoid the ffi_entry_pc wraps around and overlaps with the program or code buffer *)
  cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:64) /\
  (* the original ffi names provided does not contain MappedRead or MappedWrite *)
  (!ffis. c.ffi_names = SOME ffis ==> EVERY (λx. ∃s. x = ExtCall s) ffis ) ⇒
   implements' T (challengeMachineSem mc_conf ffi ms)
     {semantics
        (make_init mc_conf ffi t m (dm ∩ byte_aligned) (sdm ∩ byte_aligned) ms code
           (compile asm_conf) (mc_conf.target.get_pc ms + n2w (LENGTH bytes))
           cbspace coracle)}
Proof
  rw[]>>
  match_mp_tac semanticsPropsTheory.implements'_trans>>
  qho_match_abbrev_tac`∃y. implements' T y {semantics (ss (dm ∩ byte_aligned))} ∧ P y` >>
  qexists_tac`{semantics (ss dm)}` >>
  `ss (dm ∩ byte_aligned) = align_dm (ss dm)` by (
    simp[align_dm_def,Abbr`ss`,make_init_def] ) \\

  pop_assum SUBST_ALL_TAC \\
  conj_tac >- (
    match_mp_tac implements_align_dm \\
    fs[mc_conf_ok_def] ) \\
  simp[Abbr`P`,Abbr`ss`] \\

        irule semanticsPropsTheory.implements'_trans>>
  qho_match_abbrev_tac`∃y. P y ∧ implements' T y {semantics (ss (sdm ∩ byte_aligned))}` >>
  qexists_tac`{semantics (ss sdm)}` >>
  `ss (sdm ∩ byte_aligned) = align_sdm (ss sdm)` by (
    simp[Abbr`ss`,make_init_def,align_sdm_def] ) \\

  pop_assum SUBST_ALL_TAC \\
  reverse conj_tac >- (
    match_mp_tac implements_align_sdm \\
    fs[mc_conf_ok_def] ) \\
  simp[Abbr`P`,Abbr`ss`] \\

  PURE_REWRITE_TAC[Once WORD_ADD_COMM] \\
  match_mp_tac challenge_semantics_compile_lemma \\
  fs[good_code_def]
QED

val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th)
  else failwith "challenge lab compiler assumptions")
  [challenge_semantics_make_init,challenge_semantics_compile];
