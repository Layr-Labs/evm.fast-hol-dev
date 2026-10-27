(* Initial compiler simulation relation from installed code.
   Local proofs from pinned CakeML lab_to_targetProof; see ../CAKEML-LICENSE. *)
Theory initLabInitialState
Ancestors initLabSimulationHelpers
Libs preamble BasicProvers
open ffiTheory wordSemTheory labSemTheory labPropsTheory lab_to_targetTheory
  lab_filterProofTheory asmTheory asmSemTheory asmPropsTheory targetSemTheory
  targetPropsTheory backendPropsTheory lab_to_targetProofTheory
  initLabSimulationHelpersTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
Theorem UPDATE_COND_PUSH[local]:
  ∀cs rc ar (regs:num -> 'a word) g k v.
    (λa. if MEM a cs ∨ ¬(a < rc) ∨ MEM a ar then regs a else g a)⦇ k ↦ v ⦈ =
    (λa. if MEM a cs ∨ a = k ∨ ¬(a < rc) ∨ MEM a ar
         then (if a = k then v else regs a) else g a)
Proof
  rpt gen_tac \\ once_rewrite_tac[FUN_EQ_THM]
  \\ qx_gen_tac `aa` \\ rewrite_tac[APPLY_UPDATE_THM] \\ BETA_TAC
  \\ Cases_on `aa = k` \\ simp[]
QED

Theorem all_enc_ok_prog_to_bytes_EVEN[local]:
  ∀code n c labs ffi pos.
   EVEN pos ∧
   all_enc_ok c labs ffi pos code ⇒
   EVEN (LENGTH (prog_to_bytes code))
Proof
  fs[prog_to_bytes_MAP]>>
  Induct>>fs[]>>Cases>>
  fs[all_enc_ok_cons]>>rw[EVEN_ADD]>>
  rfs[]>>
  fs[LENGTH_FLAT]>>
  `MAP line_length l = MAP LENGTH (MAP line_bytes l)` by
    metis_tac[lines_ok_MAP_line_byte_length]>>
  pop_assum SUBST_ALL_TAC >>simp[]>>
  metis_tac[EVEN_ADD]
QED

Theorem find_index_MAP_w2n[local]:
  !l (x:'a word) n. find_index (w2n x) (MAP w2n l) n = find_index x l n
Proof
  Induct >> simp[find_index_def] >> rw[] >> fs[w2n_11]
QED

Theorem IMP_state_rel_make_init:
  good_code mc_conf.target.config LN (code: sec list) ∧
   mc_conf_ok mc_conf ∧
   (no_share_mem_inst code ==>
     compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes code2)) mc_conf.target.config mc_conf.ffi_names) ∧
   list_subset (FILTER (\x. ∃s. x= ExtCall s) $
      find_ffi_names code) $ TAKE i mc_conf.ffi_names ∧
   remove_labels clock mc_conf.target.config 0 LN (TAKE i mc_conf.ffi_names) code =
      SOME (code2,labs) /\
   good_init_state mc_conf ms (prog_to_bytes code2)
      cbspace t m dm sdm /\
   get_shmem_info code2 0 [] [] = (new_ffi_names, shmem_info) /\
   new_shmem_info = MAP (\rec. rec with
    <|entry_pc:= w2n (mc_conf.target.get_pc ms) + rec.entry_pc
     ;exit_pc:= w2n (mc_conf.target.get_pc ms) + rec.exit_pc|>) shmem_info /\
   DROP i mc_conf.ffi_names = new_ffi_names /\
   mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
   MAP (\rec. rec.entry_pc) new_shmem_info = DROP i (MAP w2n mc_conf.ffi_entry_pcs) /\
   (mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH new_shmem_info),
                              (MAP (\rec. (rec.nbytes,
                                Addr rec.addr_reg rec.addr_off,
                                rec.reg, n2w rec.exit_pc)) new_shmem_info))) /\
   no_install_or_no_share_mem code mc_conf.ffi_names /\
   (!bn. bn < cbspace ==>
      ~MEM (n2w bn + n2w (LENGTH (prog_to_bytes code2)) +
             mc_conf.target.get_pc ms) (TAKE i mc_conf.ffi_entry_pcs))
   ==>
   state_rel ((mc_conf: ('a,'state,'b) machine_config),code2,labs,
       mc_conf.target.get_pc ms)
     (make_init mc_conf (ffi:'ffi ffi_state) t m dm sdm ms code
      (compile_lab mc_conf.target.config)
      (mc_conf.target.get_pc ms+n2w(LENGTH(prog_to_bytes code2))) cbspace coracle) t ms
Proof
  rw[] \\ old_drule $ GEN_ALL remove_labels_thm
  \\ impl_tac >- (
    fs[good_code_def,mc_conf_ok_def]
    \\ rw[lab_lookup_def]>>
    TOP_CASE_TAC>>fs[lookup_def])
  \\ qabbrev_tac `new_shmem_info=MAP (\rec. rec with
      <|entry_pc:=w2n (mc_conf.target.get_pc ms) + rec.entry_pc
       ;exit_pc:=w2n (mc_conf.target.get_pc ms) + rec.exit_pc|>) shmem_info`
  \\ rw[]
  \\ fs[state_rel_def,
        word_loc_val_def,
        make_init_def,
        good_init_state_def,
        mc_conf_ok_def,
        compiler_oracle_ok_def,
        target_configured_def,
        good_code_def,
        start_pc_ok_def]
  \\ rfs[]
  \\ conj_tac >- suspend "ISR1"
  \\ conj_tac >- suspend "ISR2"
  \\ conj_tac >- suspend "ISR3"
  \\ conj_tac >- suspend "ISR4"
  \\ conj_tac >- suspend "ISR5"
  \\ conj_tac >- suspend "ISR6"
  \\ conj_tac >- suspend "ISR7"
  \\ conj_tac >- suspend "ISR8"
  \\ conj_tac >- suspend "ISR9"
  \\ conj_tac >- suspend "ISR10"
  \\ conj_tac >- suspend "ISR11"
  \\ conj_tac >- suspend "ISR12"
  \\ conj_tac >- suspend "ISR13"
  \\ conj_tac >- suspend "ISR14"
  \\ conj_tac >- suspend "ISR15"
  \\ conj_tac >- suspend "ISR16" >- suspend "ISR17"
QED

Resume IMP_state_rel_make_init[ISR1]:
  fs[Abbr ‘new_shmem_info’]>>
  fs[MAP_MAP_o,o_DEF]>>
  qmatch_goalsub_abbrev_tac ‘ZIP (l1,MAP ff _)’>>
  ‘LENGTH l1 = LENGTH (MAP ff shmem_info)’ by fs[Abbr ‘l1’,LENGTH_GENLIST]>>
  fs[ALOOKUP_ZIP_MAP_SND]>>
  `LENGTH shmem_info = LENGTH (DROP i (MAP w2n mc_conf.ffi_entry_pcs))`
    by (qpat_assum `MAP _ shmem_info = DROP _ _` (fn h => assume_tac (Q.AP_TERM `LENGTH` h))>>
        gvs[LENGTH_MAP,LENGTH_DROP])>>
  rw[Abbr ‘l1’]
  >- (‘shmem_info ≠ []’ by (strip_tac>>fs[])>>
      irule_at Any ALOOKUP_ALL_DISTINCT_MEM>>
      simp[MEM_ZIP,MAP_ZIP,ALL_DISTINCT_GENLIST,EL_GENLIST]>>
      qexists_tac ‘index - i’>>
      reverse conj_asm1_tac>- fs[EL_GENLIST]>>fs[LENGTH_MAP,LENGTH_DROP])>>
  rewrite_tac[ALOOKUP_FAILS]>>
  rpt strip_tac>>
  gvs[NOT_LESS,NOT_LESS_EQUAL,MEM_ZIP]
QED

Resume IMP_state_rel_make_init[ISR2]:
  rpt strip_tac
  \\ irule (REWRITE_RULE [post_ffi_asm_def] ffi_interfer_ok_post_ffi_asm)
  \\ rpt conj_tac \\ fs[]
  >- (old_drule mmio_pcs_min_index_is_SOME \\ gvs[])
  >- (conj_tac
      >- (imp_res_tac evaluatePropsTheory.call_FFI_LENGTH \\ simp[])
      \\ strip_tac \\ gvs[call_FFI_def, AllCaseEqs()])
  \\ qexists_tac `mc_conf.target.get_pc ms`
  \\ simp[]
QED

Resume IMP_state_rel_make_init[ISR3]:
  rpt strip_tac
  \\ irule (SIMP_RULE (srw_ss()) [post_install_asm_def,post_ffi_asm_def,
                                  LET_THM,UPDATE_COND_PUSH]
              install_interfer_ok_post_install_asm)
  \\ simp[]
  \\ qexistsl_tac [`cbspace`,`mc_conf.target.get_pc ms`]
  \\ simp[]
QED

Resume IMP_state_rel_make_init[ISR4]:
  ntac 2 strip_tac >>
  pairarg_tac >> fs[]>>
  drule_then assume_tac code_similar_sym >>
  drule_all_then assume_tac code_similar_IMP_both_no_share_mem >>
  fs[] >>
  qpat_x_assum`!k. _ (coracle k)`(qspec_then`k` assume_tac)>>rfs[]>>
  strip_tac>>fs[]
QED

Resume IMP_state_rel_make_init[ISR5]:
  metis_tac[EVEN,all_enc_ok_prog_to_bytes_EVEN]
QED

Resume IMP_state_rel_make_init[ISR6]:
  metis_tac[list_subset_TAKE,list_subset_trans]
QED

Resume IMP_state_rel_make_init[ISR7]:
  metis_tac[EVEN,all_enc_ok_prog_to_bytes_EVEN]
QED

Resume IMP_state_rel_make_init[ISR8]:
  imp_res_tac mmio_pcs_min_index_is_SOME>>
  rpt strip_tac>>fs[]>>
  fs[get_ffi_index_def,backendPropsTheory.the_eqn]>>
  imp_res_tac find_index_MEM>>
  first_x_assum $ qspecl_then [‘0’] assume_tac>>gvs[]
QED

Resume IMP_state_rel_make_init[ISR9]:
  simp[word_loc_val_byte_def,case_eq_thms]
  \\ metis_tac[SUBSET_DEF,word_loc_val_def]
QED

Resume IMP_state_rel_make_init[ISR10]:
  metis_tac[word_add_n2w]
QED

Resume IMP_state_rel_make_init[ISR11]:
  simp[bytes_in_mem_def]
QED

Resume IMP_state_rel_make_init[ISR12]:
  rpt strip_tac >>
  `MAP (\rec. n2w rec.entry_pc) new_shmem_info = DROP i (mc_conf.ffi_entry_pcs : 'a word list)` by (
    qpat_x_assum `MAP _ new_shmem_info = DROP i (MAP w2n _)` (fn h =>
      mp_tac (AP_TERM ``MAP (n2w:num -> 'a word)`` h)) >>
    simp[MAP_MAP_o, o_DEF, n2w_w2n, MAP_DROP]) >>
  qpat_x_assum `!bn. bn < cbspace ==> _` $ imp_res_tac >>
  gvs[MEM_EL] >>
  drule_then assume_tac $ cj 1 mmio_pcs_min_index_is_SOME>>
  gvs[LENGTH_TAKE] >>
  first_x_assum $ qspec_then`n` assume_tac >>
  Cases_on `n < i`
  >- gvs[EL_TAKE] >>
  `i <= n` by decide_tac >>
  gvs[] >>
  old_drule get_shmem_info_thm >>
  disch_then $ qspecl_then [`0`,`[]`,`[]`] assume_tac >>
  gvs[UNZIP_MAP,MAP_GENLIST,combinTheory.o_DEF,ZIP_MAP_FST_SND_EQ,MAP_MAP_o,
    Abbr`new_shmem_info`,EL_MAP] >>
  qspecl_then [`n - i`, `i`,`mc_conf.ffi_entry_pcs`]
    assume_tac $ GSYM EL_DROP >>
  gvs[] >>
  pop_assum kall_tac >>
  qpat_x_assum `_ = DROP i mc_conf.ffi_entry_pcs` $ assume_tac o GSYM >>
  fs[GSYM word_add_n2w]>>
  qmatch_assum_abbrev_tac `DROP i mc_conf.ffi_entry_pcs = MAP offset_func flatten_genlist` >>
  gvs[] >>
  `n - i < LENGTH (MAP offset_func flatten_genlist)` by (
    qpat_x_assum `DROP i mc_conf.ffi_entry_pcs = _` $ assume_tac o GSYM >>
    asm_rewrite_tac[LENGTH_DROP] >>
    simp[]
  ) >>
  gvs[EL_MAP,Abbr`offset_func`] >>
  drule_all genlist_line_to_info_entry_pc_max >>
  strip_tac >>
  drule_then (qspec_then `n-i` assume_tac) $ iffLR EVERY_EL >>
  gvs[Abbr`flatten_genlist`] >>
  qmatch_asmsub_abbrev_tac `entry_pc' < pos_val _ _ _` >>
  drule_then (fn t =>
    gvs[t,addressTheory.word_arith_lemma1]) $
    GEN_ALL pos_val_num_pcs
QED

Resume IMP_state_rel_make_init[ISR13]:
  drule pos_val_0 \\ simp[]
QED

Resume IMP_state_rel_make_init[ISR14]:
  metis_tac[code_similar_sec_labels_ok]
QED

Resume IMP_state_rel_make_init[ISR15]:
  fs[ffi_interfer_ok_def]
  \\ gvs[share_mem_state_rel_def]
  \\ rpt strip_tac
  \\ gvs[IMP_CONJ_THM, AND_IMP_INTRO]
  \\ first_x_assum $ qspecl_then [`ms2`, `k`, `index`, `new_bytes`, `t1`, `B`, `C`] mp_tac
  \\ gvs[] >> strip_tac>>fs[]>>
  old_drule mmio_pcs_min_index_is_SOME>>
  strip_tac>>fs[]>>
  first_x_assum $ qspec_then ‘index’ assume_tac>>gvs[]>>
  TOP_CASE_TAC>>fs[]
QED

Resume IMP_state_rel_make_init[ISR16]:
  simp[share_mem_domain_code_rel_def]
  \\ fs[MAP_MAP_o,o_DEF,ELIM_UNCURRY]
  \\ old_drule $ GEN_ALL get_shmem_info_ok_lemma
  \\ disch_then $ qspecl_then [
      `w2n (mc_conf.target.get_pc ms)`,`new_shmem_info`,`mc_conf.ffi_names`,
      `TAKE i mc_conf.ffi_names`] mp_tac
  \\ gvs[]
  \\ impl_tac
  >- (
    old_drule mmio_pcs_min_index_is_SOME >>
    strip_tac >>
    reverse $ rw[EVERY_EL]
   >- (
      qpat_abbrev_tac `info = get_shmem_info _ _ _ _` >>
      first_x_assum $ assume_tac o GSYM o ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
      Cases_on `info` >>
      old_drule $ GEN_ALL get_shmem_info_PREPEND >>
      gvs[] >>
      strip_tac >>
      old_drule $ GEN_ALL get_shmem_info_init_pc_offset >>
      disch_then $ qspec_then `w2n (mc_conf.target.get_pc ms)` mp_tac >>
      strip_tac >>
      gvs[markerTheory.Abbrev_def] >>
      metis_tac[TAKE_DROP] ) >>
    first_x_assum $ mp_tac o GSYM >>
    spose_not_then assume_tac >>fs[]>>
    qpat_x_assum`∀s. EL _ (TAKE i mc_conf.ffi_names) ≠ _` $ mp_tac >>
    fs[EL_TAKE]
  )
  \\ rw[]
  >- (
    qpat_x_assum `!pc op re a inst len. asm_fetch_aux _ _ = _ ==> ?i._` $ imp_res_tac
    \\ qexists `index + i`
    \\ old_drule find_index_LESS_LENGTH
    \\ fs[GSYM word_add_n2w]
    \\ `LENGTH (MAP (\rec. (n2w rec.entry_pc):'a word) new_shmem_info) =
        LENGTH mc_conf.ffi_entry_pcs - i`
          by (qpat_x_assum `MAP _ new_shmem_info = DROP _ _` (fn h =>
                assume_tac (Q.AP_TERM `LENGTH` h)) >>
              gvs[LENGTH_MAP,LENGTH_DROP])
    \\ fs[LENGTH_MAP,LESS_SUB_ADD_LESS,EL_MAP,LENGTH_TAKE]
    \\ strip_tac
    \\ `find_index (n2w (pos_val pc 0 code2) + mc_conf.target.get_pc ms)
          (DROP i mc_conf.ffi_entry_pcs) 0 = SOME index` by (
      ONCE_REWRITE_TAC[GSYM find_index_MAP_w2n] >>
      simp[MAP_DROP] >>
      `w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2 < dimword(:'a)` by (
        drule find_index_is_MEM >> strip_tac >>
        imp_res_tac MEM_DROP_IMP >>
        fs[MEM_MAP] >> metis_tac[w2n_lt]) >>
      ONCE_REWRITE_TAC[GSYM n2w_w2n |> Q.ISPEC `mc_conf.target.get_pc ms`] >>
      rewrite_tac[word_add_n2w, w2n_n2w] >>
      `pos_val pc 0 code2 < dimword(:'a)` by fs[] >>
      simp[] >>
      ONCE_REWRITE_TAC[ADD_COMM] >>
      first_x_assum ACCEPT_TAC)
    \\ old_drule find_index_shift >> fs[]
    \\ disch_then $ qspec_then `i` assume_tac
    \\ `~MEM (n2w (pos_val pc 0 code2) + mc_conf.target.get_pc ms)
          (TAKE i mc_conf.ffi_entry_pcs)` by (
      `LENGTH (prog_to_bytes code2) < dimword(:'a)` by gvs[] >>
      old_drule $ GEN_ALL asm_fetch_NOT_ffi_entry_pcs >>
      rpt $ disch_then $ drule_at Any >>
      disch_then $ qspec_then `0` mp_tac >>
      simp[line_bytes_def, line_length_def] >>
      impl_tac >- (
        old_drule $ GEN_ALL enc_ok_LENGTH_GT_0 >>
        drule_all $ GEN_ALL all_enc_ok_asm_fetch_aux_IMP_line_ok >>
        gvs[line_ok_def,line_length_def,enc_with_nop_thm] >>
        rpt strip_tac >> gvs[] >>
        first_x_assum $ qspec_then `Inst (Mem op re a)` assume_tac >> gvs[]) >>
      metis_tac[WORD_ADD_COMM, WORD_ADD_ASSOC])
    \\ `find_index (n2w (pos_val pc 0 code2) + mc_conf.target.get_pc ms)
          (TAKE i mc_conf.ffi_entry_pcs) 0 = NONE` by
      fs[GSYM find_index_NOT_MEM]
    \\ qspecl_then [
        `TAKE i (mc_conf: ('a,'state,'b) machine_config).ffi_entry_pcs`,
        `DROP i (mc_conf: ('a,'state,'b) machine_config).ffi_entry_pcs`,
        `n2w (pos_val pc 0 code2) + (mc_conf.target.get_pc ms: 'a word)`,
        `0`] assume_tac find_index_APPEND
    \\ gvs[AllCaseEqs()]
    \\ gvs[ELIM_UNCURRY,shmem_info_num_component_equality]>>
    irule ALOOKUP_ALL_DISTINCT_MEM>>
    qmatch_goalsub_abbrev_tac `ZIP (l1, l2)`>>
    `LENGTH l1 = LENGTH l2` by (unabbrev_all_tac>>fs[LENGTH_GENLIST,LENGTH_MAP])>>
    fs[MAP_ZIP,MEM_ZIP]>>unabbrev_all_tac>>fs[]>>
    fs[ALL_DISTINCT_GENLIST]>>fs[MAP_MAP_o,o_DEF]>>gvs[]>>simp[EL_MAP]>>
    qexists_tac `index`>>fs[EL_MAP]>>
    fs[EL_GENLIST]>>
    Cases_on `a` >> simp[n2w_w2n] >>
    rewrite_tac[GSYM word_add_n2w] >> simp[n2w_w2n])
  >- (
    qpat_x_assum `!pc line. asm_fetch_aux _ _ = _ /\ _ ==> _` imp_res_tac
    \\ simp[IN_DISJOINT] >> rpt strip_tac >> spose_not_then assume_tac >> gvs[]
    \\ `LENGTH (prog_to_bytes code2) < dimword(:'a)` by gvs[]
    (* TAKE case: asm_fetch_NOT_ffi_entry_pcs *)
    \\ `~MEM (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0 code2))
         (TAKE i mc_conf.ffi_entry_pcs)` by (
      irule asm_fetch_NOT_ffi_entry_pcs >> gvs[] >> metis_tac[])
    (* Get MEM in DROP via TAKE_DROP *)
    \\ `MEM (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0 code2))
         (DROP i mc_conf.ffi_entry_pcs)` by (
      ONCE_REWRITE_TAC[WORD_ADD_COMM] >>
      qpat_x_assum `MEM _ _` mp_tac >>
      `mc_conf.ffi_entry_pcs = TAKE i mc_conf.ffi_entry_pcs ++ DROP i mc_conf.ffi_entry_pcs`
        by simp[TAKE_DROP] >>
      pop_assum (fn h => ONCE_REWRITE_TAC[h]) >>
      rewrite_tac[MEM_APPEND] >> strip_tac >> gvs[])
    (* Get w2n version in DROP *)
    \\ `MEM (w2n (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0 code2)))
         (DROP i (MAP w2n mc_conf.ffi_entry_pcs))` by (
      rewrite_tac[GSYM MAP_DROP] >>
      irule MEM_MAP_f >> first_x_assum ACCEPT_TAC)
    (* w2n x >= w2n(get_pc ms) from new_shmem_info structure *)
    \\ `w2n (mc_conf.target.get_pc ms) <=
       w2n (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0 code2))` by (
      qpat_x_assum `MEM _ (DROP i (MAP w2n _))` mp_tac >>
      qpat_x_assum `MAP _ new_shmem_info = DROP i _` (SUBST1_TAC o GSYM) >>
      qpat_x_assum `Abbrev (new_shmem_info = _)` mp_tac >>
      simp[markerTheory.Abbrev_def] >> strip_tac >>
      ASM_REWRITE_TAC[] >>
      simp[MAP_MAP_o, o_DEF, MEM_MAP] >>
      strip_tac >> simp[])
    (* a + pos_val < LENGTH prog *)
    \\ `a + pos_val pc 0 code2 < LENGTH (prog_to_bytes code2)` by (
      imp_res_tac asm_fetch_aux_pos_val_SUC >>
      pop_assum $ qspec_then `0` assume_tac >>
      old_drule pos_val_bound >>
      disch_then $ qspecl_then [`pc+1`,`0`] assume_tac >>
      gvs[])
    (* Apply DISJOINT to get contradiction *)
    \\ qpat_x_assum `DISJOINT _ _` (mp_tac o REWRITE_RULE[DISJOINT_ALT])
    \\ disch_then $ qspec_then `w2n (mc_conf.target.get_pc ms + n2w a + n2w (pos_val pc 0 code2))` mp_tac
    \\ impl_tac >- (
      rewrite_tac[GSYM MAP_DROP] >>
      irule MEM_MAP_f >> first_x_assum ACCEPT_TAC)
    \\ strip_tac >> pop_assum mp_tac >> simp[]
    \\ qexists_tac `a` >> simp[]
    (* Prove w2n equality: w2n(n2w a + n2w(pos_val) + get_pc ms) = a + (w2n(pc) + pos_val) *)
    \\ ONCE_REWRITE_TAC[WORD_ADD_COMM] >> rewrite_tac[word_add_n2w]
    \\ `a + pos_val pc 0 code2 < dimword(:'a)` by fs[]
    \\ DEP_REWRITE_TAC[w2n_add_2] >> simp[w2n_n2w]
    (* Show no overflow: a + pos_val + w2n(pc) < dimword *)
    \\ spose_not_then assume_tac >> gvs[NOT_LESS]
    \\ qpat_x_assum `w2n _ <= _` mp_tac >> simp[NOT_LESS_EQUAL]
    \\ ONCE_REWRITE_TAC[WORD_ADD_COMM] >> rewrite_tac[word_add_n2w]
    \\ simp[word_add_def, w2n_n2w]
    \\ `w2n (mc_conf.target.get_pc ms) < dimword(:'a)` by simp[w2n_lt]
    \\ `a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2) < 2 * dimword(:'a)` by fs[]
    \\ `(a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2)) MOD dimword(:'a) =
       a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2) - dimword(:'a)` by (
      `0 < dimword(:'a)` by simp[] >>
      drule_all SUB_MOD >> strip_tac >>
      `a + (w2n (mc_conf.target.get_pc ms) + pos_val pc 0 code2) - dimword(:'a) < dimword(:'a)` by fs[] >>
      imp_res_tac LESS_MOD >> fs[])
    \\ simp[] >> fs[])
QED

Resume IMP_state_rel_make_init[ISR17]:
  drule_then (drule_then irule) $ GEN_ALL code_similar_IMP_both_no_install_or_no_share_mem
QED

Finalise IMP_state_rel_make_init;


val _ = if null(hyp IMP_state_rel_make_init)
  then ignore(check_thm IMP_state_rel_make_init)
  else failwith "initial lab simulation assumptions";

Theorem no_install_filter_skip:
  no_install (filter_skip code) <=> no_install code
Proof
  eq_tac >- (
    gvs[no_install_def] >>
    spose_not_then assume_tac >>
    rw[] >>
    last_x_assum mp_tac >>
    simp[] >>
    old_drule IMP_asm_fetch_aux_filter_skip >>
    simp[lab_filterTheory.not_skip_def] >>
    metis_tac[]) >>
  gvs[no_install_def] >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  fs[] >>
  old_drule asm_fetch_aux_filter_skip >>
  gvs[lab_filterTheory.not_skip_def] >>
  metis_tac[]
QED
val _ = if null(hyp no_install_filter_skip) then ignore(check_thm no_install_filter_skip)
  else failwith "no-install filtering assumptions";
