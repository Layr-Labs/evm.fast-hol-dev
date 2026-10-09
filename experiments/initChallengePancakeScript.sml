(* Adapted from pinned CakeML pan_to_targetProof; see ../CAKEML-LICENSE. *)
(*

composing semantics correctness from pan to target

*)
Theory initChallengePancake
Ancestors
  initChallengeLabCompiler pan_to_targetProof
  backendProof stackProps stack_to_labProof lab_to_targetProof
  pan_to_wordProof pan_to_target wordConvsProof
Libs
  preamble blastLib[qualified]


Overload stack_remove_prog_comp[local] = ``stack_remove$prog_comp``
Overload stack_alloc_prog_comp[local] = ``stack_alloc$prog_comp``
Overload stack_names_prog_comp[local] = ``stack_names$prog_comp``
Overload word_to_word_compile[local] = ``word_to_word$compile``
Overload word_to_stack_compile[local] = ``word_to_stack$compile``
Overload stack_to_lab_compile[local] = ``stack_to_lab$compile``
Overload pan_to_word_compile_prog[local] = ``pan_to_word$compile_prog``

val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem n2w_sub_alt[local]:
  ∀a b. b ≤ a ⇒ n2w (a - b) = n2w a + -1w * n2w b
Proof
  rpt strip_tac >>
  irule EQ_TRANS >>
  drule_then (irule_at (Pos hd)) n2w_sub >>
  simp[] >>
  metis_tac[WORD_NEG_MUL]
QED

Theorem aligned_n2w_IMP[local]:
  aligned k ((n2w n):'a word) ∧ n < dimword(:'a) ⇒ divides (2**k) n
Proof
  rw[aligned_w2n,dimword_def] >>
  gvs[dividesTheory.DIVIDES_MOD_0]
QED

val from_pan_to_lab_no_install = INST_TYPE [alpha |-> ``:64``]
  pan_to_targetProofTheory.from_pan_to_lab_no_install;
val pan_to_lab_good_code_lemma = INST_TYPE [alpha |-> ``:64``]
  pan_to_targetProofTheory.pan_to_lab_good_code_lemma;

val word_to_stack_good_code_lemma = SIMP_RULE (srw_ss()) []
  (INST_TYPE [alpha |-> ``:64``] pan_to_targetProofTheory.word_to_stack_good_code_lemma);

val w2n_lt = SIMP_RULE (srw_ss()) []
  (INST_TYPE [alpha |-> ``:64``] wordsTheory.w2n_lt);

val byte_aligned_mult = SIMP_RULE (srw_ss())
  [bytes_in_word_def,miscTheory.good_dimindex_def]
  (INST_TYPE [alpha |-> ``:64``] backendProofTheory.byte_aligned_mult);

Theorem native_globals_split[local]:
  !i global_words heap_words.
    heap_words <= i + global_words ==>
    8*i MOD 18446744073709551616 =
    (8*(i+global_words-heap_words) +
     (8*heap_words +
      (18446744073709551616 - 8*global_words MOD 18446744073709551616))) MOD
    18446744073709551616
Proof
  intLib.ARITH_TAC
QED

Theorem native_globals_join[local]:
  !i global_words heap_words.
    global_words <= heap_words ==>
    (8*i + (8*heap_words +
      (18446744073709551616 - 8*global_words MOD 18446744073709551616))) MOD
    18446744073709551616 =
    8*(i+heap_words-global_words) MOD 18446744073709551616
Proof
  intLib.ARITH_TAC
QED

Theorem challenge_pan_to_target_compile_semantics:
  compile_prog_max c mc pan_code = (SOME (bytes, bitmaps, c'), stack_max) ∧
  pancake_good_code pan_code ∧
  distinct_params (functions pan_code) ∧
  ALL_DISTINCT (MAP FST(functions pan_code)) ∧
  s.code = FEMPTY ∧
  s.locals = FEMPTY ∧
  s.globals = FEMPTY ∧
  size_of_eids pan_code < dimword (:64) ∧
  s.eshapes = FEMPTY ∧
  backend_config_ok mc.target.config c ∧ lab_to_targetProof$mc_conf_ok mc ∧
  mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
  0w <₊ mc.target.get_reg ms mc.len_reg ∧
  globals_size = (let dec_shs = dec_shapes pan_code;
    struct_ctxt = panSem$decs_stcnames [] pan_code
  in SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) ∧
  mc.target.get_reg ms mc.len_reg  <₊ mc.target.get_reg ms mc.ptr2_reg ∧
  mc.target.get_reg ms mc.len_reg = s.base_addr ∧
  globals_allocatable s pan_code ∧
  heap_len = w2n ((mc.target.get_reg ms mc.ptr2_reg) + -1w * s.base_addr) DIV (dimindex (:64) DIV 8) ∧
  s.top_addr = s.base_addr + bytes_in_word * n2w heap_len - n2w(globals_size*dimindex (:64) DIV 8) ∧
  globals_size ≤ heap_len ∧
  s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg) (heap_len-globals_size) ∧
  aligned (backend_common$word_shift (dimindex (:64)) + 1) ((mc.target.get_reg ms mc.ptr2_reg) + -1w * (mc.target.get_reg ms mc.len_reg)) ∧
  adj_ptr2 = (mc.target.get_reg ms mc.len_reg) + bytes_in_word * n2w max_stack_alloc ∧
  adj_ptr4 = (mc.target.get_reg ms mc.len2_reg) - bytes_in_word * n2w max_stack_alloc ∧
  adj_ptr2 ≤₊ (mc.target.get_reg ms mc.ptr2_reg) ∧
  (mc.target.get_reg ms mc.ptr2_reg) ≤₊ adj_ptr4 ∧
  w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * (mc.target.get_reg ms mc.len_reg)) ≤
  w2n (bytes_in_word:64 word) * (2 * max_heap_limit (dimindex (:64)) c.data_conf -1) ∧
  w2n (bytes_in_word:64 word) * (2 * max_heap_limit (dimindex (:64)) c.data_conf -1) < dimword (:64) ∧
  s.ffi = ffi ∧ mc.target.config.big_endian = s.be ∧
  OPTION_ALL (EVERY $ \x. ∃s. x = ExtCall s) c.lab_conf.ffi_names ∧
  pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
                (heap_regs c.stack_conf.reg_names) mc
                c'.lab_conf.shmem_extra ms
                (wlab_wloc o s.memory)
                s.memaddrs s.sh_memaddrs ∧
  start = «main» ∧
  semantics_decls s start pan_code ≠ Fail ⇒
  challengeMachineSem (mc:(64,riscv_state,γ) machine_config) (ffi:'ffi ffi_state) ms ⊆
              extend_with_resource_limit'
              (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
              {semantics_decls (s:(64,'ffi) panSem$state) start pan_code}
Proof

  strip_tac>>
  last_x_assum mp_tac>>
  rewrite_tac[compile_prog_max_def]>>
  rewrite_tac[backendTheory.from_stack_def]>>
  rewrite_tac[backendTheory.from_lab_def]>>
  strip_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  rename1 ‘_ = (col, wprog)’>>
  qmatch_asmsub_abbrev_tac ‘attach_bitmaps _ _ _ tprog = _’>>
  qmatch_asmsub_abbrev_tac ‘Abbrev (_ = compile _ _ lprog)’>>
  (* unfolding done *)

  (* apply lab_to_target *)
  irule SUBSET_TRANS>>
  irule_at Any (initChallengeLabCompilerTheory.challenge_semantics_compile |>
                  REWRITE_RULE [semanticsPropsTheory.implements'_def,
                                semanticsPropsTheory.extend_with_resource_limit'_def])>>

  qpat_x_assum ‘Abbrev (tprog = _)’
               (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
  Cases_on ‘tprog’>>gs[backendTheory.attach_bitmaps_def]>>
  rename1 ‘compile _ _ _ = SOME x’>>Cases_on ‘x’>>
  rename1 ‘compile _ _ _ = SOME (tprog, ltconf)’>>
  gs[]>>
  qabbrev_tac ‘hp = heap_regs c.stack_conf.reg_names’>>
  Cases_on ‘hp’>>gs[]>>

  (* no_install_or_no_share_mem *)
  ‘no_install lprog’ by
    (fs[Abbr ‘lprog’]>>
     irule from_pan_to_lab_no_install>>
     rpt (first_assum $ irule_at Any)>>
     metis_tac[mc_init_ok_def])>>
  ‘no_install_or_no_share_mem lprog mc.ffi_names’
    by fs[lab_to_targetProofTheory.no_install_or_no_share_mem_def]>>

  (* compiler_orackle_ok *)
  qmatch_asmsub_abbrev_tac ‘stack_to_lab_compile _ _ _ max_heap sp _ _’>>
  qabbrev_tac ‘lorac = λn:num.
                         (ltconf, []:(num # stack_rawcallProof$prog) list, []:64 word list)’>>
  qabbrev_tac ‘sorac =
               (λn:num.
                  (λ(c',p,b:64 word list).
                     (c',
                      compile_no_stubs (arch_wordsize mc.target.config.ISA) c.stack_conf.reg_names
                                       c.stack_conf.jump
                                       mc.target.config.addr_offset sp p))
                  (lorac n))’>>

  imp_res_tac backendProofTheory.compile_to_word_conventions2>>
  gs[backendProofTheory.mc_init_ok_def]>>
  gs[backendTheory.attach_bitmaps_def]>>
  gs[backendProofTheory.backend_config_ok_def]>>
  gs[pan_installed_def]>>gs[]>>

  ‘no_share_mem_inst lprog ⇒
   compiler_oracle_ok sorac ltconf.labels (LENGTH bytes)
                      mc.target.config mc.ffi_names’
    by (
    gs[Abbr ‘sorac’]>>gs[Abbr ‘lorac’]>>
    simp [lab_to_targetProofTheory.compiler_oracle_ok_def]>>
    ‘ltconf.pos = LENGTH bytes’
      by (gs[lab_to_targetTheory.compile_def]>>
          drule backendProofTheory.compile_lab_LENGTH>>
          strip_tac>>gs[])>>gs[]>>
    gvs[stack_to_labTheory.compile_no_stubs_def]>>
    gs[stack_namesTheory.compile_def]>>
    gs[lab_to_targetProofTheory.good_code_def]>>
    gs[labPropsTheory.get_labels_def,backendPropsTheory.restrict_nonzero_def]>>
    fs[labPropsTheory.no_share_mem_inst_def,labSemTheory.asm_fetch_aux_def])>>
  first_assum $ irule_at Any>>gs[]>> (* no_install_or_no_share_mem *)
  first_assum $ irule_at Any>>gs[]>>  (* lab_to_target$compile *)

  ‘EVERY (λ(_,_,_). T) (pan_to_word_compile_prog mc.target.config.ISA pan_code)’ by
    (rw[]>>simp[EVERY_MEM,FORALL_PROD])>>fs[]>>

  ‘good_code mc.target.config (LN:num sptree$num_map sptree$num_map) lprog’
    by (
    irule (INST_TYPE [beta|-> ``:num``] pan_to_lab_good_code_lemma)>>
    gs[]>>
    rpt (first_assum $ irule_at Any)>>
    qpat_x_assum ‘Abbrev (lprog = _)’
                 (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
    first_assum $ irule_at Any>>
    qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
    qpat_x_assum ‘Abbrev (wprog0 = _)’
                 (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
    (* labels_ok *)
    drule_all pan_to_lab_labels_ok>>strip_tac>>gs[]>>
    (* all_enc_ok_pre mc.target.config lprog *)
    ‘byte_offset_ok mc.target.config 0’
      by gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
    gs[stack_to_labTheory.compile_def]>>rveq>>
    irule stack_to_labProofTheory.compile_all_enc_ok_pre>>gs[]>>
    (irule stack_namesProofTheory.stack_names_stack_asm_ok>>
     gs[]>>
     irule (INST_TYPE [alpha |-> ``:64``] stack_removeProofTheory.stack_remove_stack_asm_name)>>
     gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
     gs[stackPropsTheory.reg_name_def, Abbr ‘sp’]>>
     irule (INST_TYPE [alpha |-> ``:64``] stack_allocProofTheory.stack_alloc_stack_asm_convs)>>
     gs[stackPropsTheory.reg_name_def]>>
     assume_tac (GEN_ALL stack_rawcallProofTheory.stack_alloc_stack_asm_convs)>>

     first_x_assum (qspecl_then [‘p’, ‘mc.target.config’] assume_tac)>>gs[]>>
     (* reshaping... *)
     gs[GSYM EVERY_CONJ]>>
     simp[LAMBDA_PROD]>>
     ‘p = SND (SND (SND (word_to_stack_compile mc.target.config F wprog)))’
       by gs[]>>
     pop_assum $ (fn h => rewrite_tac[h])>>
     irule word_to_stackProofTheory.word_to_stack_stack_asm_convs>>
     gs[]>>
     irule EVERY_MONOTONIC>>
     qpat_assum ‘EVERY _ wprog’ $ irule_at Any>>
     rpt strip_tac>>pairarg_tac>>gs[]>>
     first_x_assum $ irule>>
     irule pan_to_word_every_inst_ok_less>>
     conj_tac >- (qexists_tac ‘pan_code’>>gs[pancake_good_code_def])>>
     gs[])>>
    gs[])>>
  gs[]>>
  first_assum $ irule_at Any>>gs[]>>
  simp[Once SWAP_EXISTS_THM]>>
  qexists_tac ‘sorac’>>fs[]>>
  ‘ltconf = c'.lab_conf’ by gvs[]>>gs[]>>

  qpat_assum ‘compile _ _ lprog = SOME _’ mp_tac>>
  rewrite_tac[lab_to_targetTheory.compile_def]>>strip_tac>>
  drule_all backendProofTheory.compile_lab_IMP_mmio_pcs_min_index>>
  strip_tac>>
  fs[]>>rfs[]>>
  conj_tac>- (Cases_on ‘c.lab_conf.ffi_names’>>fs[])>>

  qmatch_goalsub_abbrev_tac ‘labSem$semantics labst’>>

  mp_tac (GEN_ALL stack_to_labProofTheory.full_make_init_semantics
            |> INST_TYPE [alpha |-> ``:64``, beta|-> “:lab_to_target$config”, gamma|-> “:'ffi”])>>

  gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
  disch_then (qspec_then ‘labst’ mp_tac)>>gs[]>>
  ‘labst.code = stack_to_lab_compile
                (arch_wordsize mc.target.config.ISA) c.stack_conf c.data_conf
                (2 * max_heap_limit (dimindex (:64)) c.data_conf − 1)
                (mc.target.config.reg_count −
                 (LENGTH mc.target.config.avoid_regs + 3))
                mc.target.config.addr_offset p’
    by gs[Abbr ‘labst’, Abbr ‘lprog’,lab_to_targetProofTheory.make_init_def]>>
  disch_then $ drule_at Any>>gs[]>>
  qabbrev_tac ‘sopt =
               full_make_init (arch_wordsize mc.target.config.ISA) c.stack_conf c.data_conf max_heap
                              sp mc.target.config.addr_offset
                              bitmaps p labst
                              (set mc.callee_saved_regs) data_sp lorac’>>
  Cases_on ‘sopt’>>gs[]>>
  rename1 ‘_ = (sst, opt)’>>
  disch_then $ drule_at (Pos hd)>>
  ‘labst.compile_oracle =
   (λn. (λ(c',p,b).
           (c', compile_no_stubs (arch_wordsize mc.target.config.ISA) c.stack_conf.reg_names c.stack_conf.jump
                                 mc.target.config.addr_offset sp p)) (lorac n))’
    by gs[Abbr ‘labst’, Abbr ‘sorac’,lab_to_targetProofTheory.make_init_def]>>
  gs[]>>
  ‘¬MEM labst.link_reg mc.callee_saved_regs ∧ labst.pc = 0 ∧
   (∀k i n. MEM k mc.callee_saved_regs ⇒ labst.io_regs n i k = NONE) ∧
   (∀k n. MEM k mc.callee_saved_regs ⇒ labst.cc_regs n k = NONE) ∧
   (∀x. x ∈ labst.mem_domain ⇒ w2n x MOD (dimindex (:64) DIV 8) = 0) ∧
   (∀x. x ∈ labst.shared_mem_domain ⇒ w2n x MOD (dimindex (:64) DIV 8) = 0) ∧
   good_code sp p ∧ (∀n. good_code sp (FST (SND (lorac n)))) ∧
   10 ≤ sp ∧
   (MEM (find_name c.stack_conf.reg_names (sp + 1))
    mc.callee_saved_regs ∧
    MEM (find_name c.stack_conf.reg_names (sp + 2))
        mc.callee_saved_regs) ∧ mc.len2_reg = labst.len2_reg ∧
   mc.ptr2_reg = labst.ptr2_reg ∧ mc.len_reg = labst.len_reg ∧
   mc.ptr_reg = labst.ptr_reg ∧ labst.shared_mem_domain = s.sh_memaddrs ∧
   (case mc.target.config.link_reg of NONE => 0 | SOME n => n) =
   labst.link_reg ∧ ¬labst.failed’
    by (gs[Abbr ‘labst’, Abbr ‘sp’,
           lab_to_targetProofTheory.make_init_def,
           targetPropsTheory.target_io_regs_callee_saved,
           targetPropsTheory.target_cc_regs_callee_saved]>>
        gs[Abbr ‘lorac’]>>
        drule backendProofTheory.byte_aligned_MOD>>gs[]>>
        strip_tac>>
        drule_all word_to_stack_good_code_lemma>>
        rw[]>>
        gs[stack_to_labProofTheory.good_code_def])>>
  gs[]>>

  ‘memory_assumption c.stack_conf.reg_names bitmaps data_sp labst’
    by (
    gs[stack_to_labProofTheory.memory_assumption_def]>>
    qpat_assum ‘Abbrev (labst = _)’ mp_tac>>
    rewrite_tac[markerTheory.Abbrev_def]>>
    rewrite_tac[lab_to_targetProofTheory.make_init_def,
                labSemTheory.state_component_equality]>>
    simp[]>>strip_tac>>gs[]>>
    gs[backendProofTheory.heap_regs_def]>>

    qpat_x_assum ‘_ (fun2set _)’ assume_tac>>

    rewrite_tac[Once INTER_COMM]>>
    rewrite_tac[UNION_OVER_INTER]>>
    rewrite_tac[Once UNION_COMM]>>
    irule miscTheory.fun2set_disjoint_union>>
    gs[]>>
    conj_tac >- (
      irule backendProofTheory.word_list_exists_imp>>
      gs[]>>
      ‘(w2n:64 word -> num) bytes_in_word = dimindex (:64) DIV 8’ by
        rfs [miscTheory.good_dimindex_def,bytes_in_word_def,dimword_def]>>
      conj_tac >- (
        fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
        \\ rfs [miscTheory.good_dimindex_def])>>
      fs [stack_removeProofTheory.addresses_thm]>>
      ‘0 < dimindex (:64) DIV 8’ by
        rfs [miscTheory.good_dimindex_def]>>
      gs[]
      \\ qabbrev_tac `a = t.regs q`
      \\ qabbrev_tac `b = t.regs r`
      \\ qpat_x_assum `a <=+ b` assume_tac
      \\ old_drule WORD_LS_IMP \\ strip_tac \\ fs [EXTENSION]
      \\ fs [IN_DEF,PULL_EXISTS,bytes_in_word_def,word_mul_n2w]
      \\ rw [] \\ reverse eq_tac THEN1
       (rw [] \\ fs [] \\ qexists_tac `i * (dimindex (:64) DIV 8)` \\ fs []
        \\ `0 < dimindex (:64) DIV 8` by rfs [miscTheory.good_dimindex_def]
        \\ old_drule X_LT_DIV \\ disch_then (fn th => fs [th])
        \\ fs [RIGHT_ADD_DISTRIB]
        \\ fs [GSYM word_mul_n2w,GSYM bytes_in_word_def]
        \\ fs [byte_aligned_mult] \\ intLib.ARITH_TAC)
      \\ rw [] \\ fs []
      \\ `i < dimword (:64)` by (simp[dimword_64] \\ irule LESS_TRANS
          \\ first_assum (irule_at Any) \\ simp[w2n_lt]) \\ fs []
      \\ qexists_tac `i DIV (dimindex (:64) DIV 8)`
      \\ rfs [alignmentTheory.byte_aligned_def,
              ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
      \\ fs [aligned_w2n]
      \\ old_drule DIVISION
      \\ disch_then (qspec_then `i` (strip_assume_tac o GSYM))
      \\ `2 ** LOG2 (dimindex (:64) DIV 8) = dimindex (:64) DIV 8` by
        (fs [miscTheory.good_dimindex_def] \\ NO_TAC)
      \\ fs [] \\ rfs [] \\ `-1w * a + b = b - a` by fs []
      \\ full_simp_tac std_ss []
      \\ Cases_on `a` \\ Cases_on `b`
      \\ full_simp_tac std_ss [WORD_LS,addressTheory.word_arith_lemma2]
      \\ fs []
      \\ `~(n' < n) /\ n' - n < 18446744073709551616` by intLib.ARITH_TAC
      \\ fs []
      \\ map_every (fn q => qpat_x_assum q mp_tac)
           [`i MOD 8 = 0`,`n MOD 8 = 0`,`n' MOD 8 = 0`,
            `i < n' - n`,`i < 18446744073709551616`]
      \\ POP_ASSUM_LIST (K ALL_TAC) \\ intLib.ARITH_TAC)>>
    irule DISJOINT_INTER>>gs[DISJOINT_SYM])>>
  gs[]>>

  (* apply stack_to_lab *)
  strip_tac>>
  ‘semantics InitGlobals_location sst ≠ Fail ⇒
   semantics labst ≠ Fail’ by rw[]>>
  pop_assum $ irule_at Any>>

  irule_at Any $ METIS_PROVE [] “∀x y z. x = y ∧ y ∈ z ⇒ x ∈ z”>>
  pop_assum $ irule_at Any>>

  (* word_to_stack *)

  (* instantiate / discharge *)
  ‘FST (word_to_stack_compile mc.target.config F wprog) ≼ sst.bitmaps ∧
   sst.code = fromAList p’
    by (
    gs[stack_to_labProofTheory.full_make_init_def]>>
    gs[stack_removeProofTheory.make_init_opt_def]>>
    Cases_on ‘opt’>>gs[]>>
    gs[stack_removeProofTheory.make_init_any_def,
       stack_allocProofTheory.make_init_def,
       stack_to_labProofTheory.make_init_def,
       stack_namesProofTheory.make_init_def]>>
    qmatch_asmsub_abbrev_tac ‘evaluate (init_code _ gengc _ _, s')’>>
    qmatch_asmsub_abbrev_tac ‘make_init_opt _ _ _ _ _ coracle jump off _ code _’>>
    Cases_on ‘evaluate (init_code (arch_wordsize mc.target.config.ISA) gengc max_heap sp, s')’>>gs[]>>
    rename1 ‘evaluate _ = (q', r')’>>
    Cases_on ‘q'’>>gs[]>>rveq>>
    gs[stackSemTheory.state_component_equality]>>
    Cases_on ‘make_init_opt (arch_wordsize mc.target.config.ISA) gengc max_heap bitmaps data_sp coracle jump off sp code s'’>>
    gs[stackSemTheory.state_component_equality]>>
    gs[stack_removeProofTheory.make_init_opt_def]>>
    gs[stack_removeProofTheory.init_reduce_def]>>
    gs[stack_removeProofTheory.init_prop_def]>>
    rveq>>gs[stackSemTheory.state_component_equality])>>

  ‘sst.code = fromAList (SND (SND (SND (word_to_stack_compile mc.target.config F wprog))))’
    by gs[]>>
  drule_at Any word_to_stackProofTheory.compile_semantics>>
  gs[]>>

  ‘EVERY (λ(n,m,prog).
            flat_exp_conventions prog ∧
            post_alloc_conventions
            (mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 5)) prog) wprog’
    by (qpat_x_assum ‘EVERY _ wprog’ assume_tac>>
        gs[EVERY_EL]>>rpt strip_tac>>
        first_x_assum $ qspec_then ‘n’ assume_tac>>
        pairarg_tac>>gs[])>>gs[]>>
  disch_then (qspec_then ‘InitGlobals_location’ mp_tac)>>
  disch_then (qspec_then ‘λn. ((LENGTH bitmaps, c'.lab_conf), [])’ mp_tac)>>

  qmatch_goalsub_abbrev_tac ‘init_state_ok _ _ _ worac’>>

  ‘¬ NULL bitmaps ∧ HD bitmaps = 4w’
    by (drule word_to_stackProofTheory.compile_word_to_stack_bitmaps>>
        strip_tac>>Cases_on ‘bitmaps’>>gs[])>>
  ‘ALOOKUP wprog raise_stub_location = NONE ∧
   ALOOKUP wprog store_consts_stub_location = NONE’
    by (
    qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
    qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
    drule pan_to_word_compile_prog_lab_min>>
    gs[GSYM EVERY_MAP]>>
    rewrite_tac[ALOOKUP_NONE, EVERY_MEM]>>
    qpat_x_assum ‘MAP FST _ = MAP FST _’ $ assume_tac o GSYM>>
    strip_tac>>gs[]>>
    gs[wordLangTheory.raise_stub_location_def, EL_MAP,
       wordLangTheory.store_consts_stub_location_def,
       backend_commonTheory.word_num_stubs_def,
       backend_commonTheory.stack_num_stubs_def]>>
    first_assum $ qspec_then ‘5’ assume_tac>>
    first_x_assum $ qspec_then ‘6’ assume_tac>>gs[])>>gs[]>>

  ‘init_state_ok
   mc.target.config
   (mc.target.config.reg_count −
    (LENGTH mc.target.config.avoid_regs + 5)) sst worac’
    by (
    irule stack_to_labProofTheory.IMP_init_state_ok>>
    gs[]>>
    Cases_on ‘opt’>>gs[]>>rename1 ‘(sst, SOME xxx)’>>
    MAP_EVERY qexists_tac [‘arch_wordsize mc.target.config.ISA’, ‘data_sp’, ‘c.data_conf’, ‘labst’, ‘max_heap’, ‘p’, ‘set mc.callee_saved_regs’,
                           ‘c.stack_conf’, ‘sp’, ‘mc.target.config.addr_offset’, ‘TL bitmaps’, ‘xxx’]>>

    ‘4w::TL bitmaps = bitmaps’ by (rveq>>gs[]>>metis_tac[CONS])>>gs[]>>
    conj_tac >-
     (strip_tac>>gs[Abbr ‘worac’]>>strip_tac>>
      pop_assum kall_tac>>
      pop_assum (fn h => once_rewrite_tac[GSYM h])>>gs[])>>
    gs[Abbr ‘worac’]>>
    qpat_x_assum ‘_ = (sst, SOME _)’ mp_tac>>
    gs[Abbr ‘lorac’]>>
    pairarg_tac>>gs[]>>
    gs[word_to_stackTheory.compile_def]>>
    pairarg_tac>>gs[]>>
    gs[word_to_stackTheory.compile_word_to_stack_def]>>
    rveq>>gs[]>>rw[])>>gs[]>>

  (* apply word_to_stack *)
  qmatch_goalsub_abbrev_tac ‘wordSem$semantics wst _’>>
  strip_tac>>

  (* elim stackSem ≠ Fail *)
  ‘semantics wst InitGlobals_location ≠ Fail ⇒
   semantics InitGlobals_location sst ≠ Fail’
    by (rw[]>>
        gs[semanticsPropsTheory.extend_with_resource_limit'_def]>>
        gs[semanticsPropsTheory.extend_with_resource_limit_def]>>
        FULL_CASE_TAC>>gs[])>>
  pop_assum $ irule_at Any>>

  ‘semantics wst InitGlobals_location ≠ Fail ⇒
   (∀res t k. evaluate (Call NONE (SOME InitGlobals_location) [0] NONE, wst with clock := k) = (res, t) ⇒ res ≠ SOME Error)’
    by (simp[wordSemTheory.semantics_def]>>
        IF_CASES_TAC>>gs[]>>
        rpt strip_tac>>
        first_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>

  (* actually apply word_to_stack *)
  irule_at Any $ METIS_PROVE [SUBSET_DEF] “∀z A B. A ⊆ B ∧ z ∈ A ⇒ z ∈ B”>>
  first_x_assum $ irule_at Any>>

  gs[semanticsPropsTheory.extend_with_resource_limit'_def]>>

  ‘∀(x:behaviour set) y a b f. x = y ∧ (b ⇒ a) ∧ (∀x. x ⊆ f x) ⇒ (if a then x else f x) ⊆ (if b then y else f y)’
    by (rpt strip_tac>>IF_CASES_TAC>>gs[]>>IF_CASES_TAC>>gs[])>>
  pop_assum $ irule_at Any>>

  (* word_to_word *)
  drule (word_to_wordProofTheory.word_to_word_compile_semantics |> INST_TYPE [beta |-> “: num # lab_to_target$config”])>>

  disch_then (qspecl_then [‘wst’, ‘InitGlobals_location’, ‘wst with code := fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)’] mp_tac)>>
  gs[]>>
  ‘gc_fun_const_ok wst.gc_fun ∧
   no_install_code (fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)) ∧
   no_alloc_code (fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)) ∧
   no_mt_code (fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code))’
    by (conj_tac >- (
         gs[Abbr ‘wst’, word_to_stackProofTheory.make_init_def]>>
         gs[stack_to_labProofTheory.full_make_init_def,
            stack_removeProofTheory.make_init_opt_def]>>
         Cases_on ‘opt’>>gs[]>>
         gs[stack_removeProofTheory.make_init_any_def,
            stack_allocProofTheory.make_init_def,
            stack_to_labProofTheory.make_init_def,
            stack_namesProofTheory.make_init_def]>>
         rveq>>
         gs[stackSemTheory.state_component_equality]>>
         irule data_to_word_gcProofTheory.gc_fun_const_ok_word_gc_fun)>>
        conj_tac >- (
         irule pan_to_word_compile_prog_no_install_code>>
         metis_tac[])>>
        conj_tac >- (
         irule pan_to_word_compile_prog_no_alloc_code>>
         metis_tac[])>>
        irule pan_to_word_compile_prog_no_mt_code>>
        metis_tac[])>>gs[]>>
  ‘ALL_DISTINCT (MAP FST (pan_to_word_compile_prog mc.target.config.ISA pan_code)) ∧
   wst.stack = [] ∧ wst.code = fromAList wprog ∧
   lookup 0 wst.locals = SOME (Loc 1 0) ∧
   wst = wst with code := wst.code’
    by (
    drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
    strip_tac>>
    gs[Abbr ‘wst’, word_to_stackProofTheory.make_init_def])>>gs[]>>

  (* remove wordSem1 ≠ Fail *)
  qmatch_goalsub_abbrev_tac ‘fromAList wprog0’>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac ‘semantics wst0 _ ≠ Fail’>>
  ‘semantics wst0 InitGlobals_location ≠ Fail ⇒
   semantics wst InitGlobals_location ≠ Fail’
    by (rw[]>>gs[])>>
  pop_assum $ irule_at Any>>

  ‘semantics wst0 InitGlobals_location ≠ Fail ⇒
         ∀t k. evaluate (Call NONE (SOME InitGlobals_location) [0] NONE,wst with clock := k) ≠ (SOME Error,t)’
    by (strip_tac>>gs[])>>
  qpat_x_assum ‘semantics wst _ ≠ Fail ⇒ _’ kall_tac>>

  (* apply word_to_word *)
  irule_at Any EQ_TRANS>>
  qpat_x_assum ‘_ ≠ Fail ⇒ _ = _’ $ (irule_at Any) o GSYM>>
  gs[]>>rewrite_tac[Once CONJ_COMM]>>
  gs[GSYM CONJ_ASSOC]>>

  (* misc *)
  ‘(wst.be ⇔ s.be) ∧ wst.ffi = ffi’
    (* prove this before unfolding full_make_init *)
    by (gs[Abbr ‘wst’,
           word_to_stackProofTheory.make_init_def]>>
        qmatch_asmsub_abbrev_tac ‘fmi = (sst, opt)’>>
        ‘sst = FST fmi’ by gs[]>>gs[]>>
        conj_tac
        >- (fs[Abbr ‘fmi’]>>
            gs[full_make_init_be]>>
            qpat_x_assum ‘Abbrev (labst = _)’ ((fn h => rewrite_tac[h]) o REWRITE_RULE [markerTheory.Abbrev_def])>>
            rewrite_tac[lab_to_targetProofTheory.make_init_def]>>
            simp[labSemTheory.state_component_equality])>>
        ‘labst.ffi = ffi’
          by (gs[Abbr ‘labst’, lab_to_targetProofTheory.make_init_simp])>>
        irule EQ_TRANS>>pop_assum $ irule_at Any>>
        fs[Abbr ‘fmi’]>>gs[stack_to_labProofTheory.full_make_init_ffi])>>gs[]>>

  (* move init_code_thm here *)
  (* first, take apart full_make_init to expose init_code *)
  qpat_x_assum ‘_ = (sst, opt)’ mp_tac>>

  simp[stack_to_labProofTheory.full_make_init_def]>>
  simp[stack_removeProofTheory.make_init_opt_def,
       stack_allocProofTheory.make_init_def,
       stack_namesProofTheory.make_init_def,
       stack_to_labProofTheory.make_init_def,
       stack_removeProofTheory.make_init_any_def]>>
  Cases_on ‘opt’>>gs[Abbr ‘lorac’]>>
  qmatch_goalsub_abbrev_tac ‘evaluate (initc, ssx)’>>
  Cases_on ‘evaluate (initc, ssx)’>>gs[]>>
  rename1 ‘evaluate (_,ssx) = (res,sss)’>>
  Cases_on ‘res’>>gs[]>>

  qpat_x_assum ‘_ = labst.len2_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.ptr2_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.len_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.ptr_reg’ $ assume_tac o GSYM>>
  fs[heap_regs_def]>>
  qpat_x_assum ‘_ = q’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = r’ $ assume_tac o GSYM>>
  gs[]>>ntac 2 $ pop_assum kall_tac>>

  ‘mc.len2_reg ≠ mc.len_reg ∧ mc.ptr2_reg ≠ mc.len_reg ∧
   mc.len2_reg ≠ mc.ptr2_reg’
    by (
    gs[BIJ_DEF, INJ_DEF]>>
    conj_tac >- (
      CCONTR_TAC>>
      last_x_assum $ qspecl_then [‘4’, ‘2’] assume_tac>>
      gs[])>>
    conj_tac >- (
      CCONTR_TAC>>
      last_x_assum $ qspecl_then [‘3’, ‘2’] assume_tac>>
      gs[])>>
    CCONTR_TAC>>
    last_x_assum $ qspecl_then [‘3’, ‘4’] assume_tac>>
    gs[])>>

  qmatch_goalsub_abbrev_tac ‘init_reduce _ gck jump off _ mprog _ _ _ _’>>
  simp[o_DEF]>>strip_tac>>gs[]>>

  (* introduce init_code_thm *)
  ‘lookup stack_err_lab ssx.code = SOME (halt_inst 2)’
    by
    (gs[Abbr ‘ssx’]>>
     gs[lookup_fromAList,stack_removeTheory.compile_def]>>
     gs[stack_removeTheory.init_stubs_def,
        stack_removeTheory.stack_err_lab_def])>>
  gs[Abbr ‘initc’]>>
  drule_at Any stack_removeProofTheory.init_code_thm>>
  ‘ssx.compile_oracle =
   (I ## MAP (stack_remove_prog_comp (arch_wordsize mc.target.config.ISA) jump off sp) ## I)
   ∘ (I ## MAP stack_alloc_prog_comp ## I) ∘ (λn. (ltconf,[],[]))’
    by gs[Abbr ‘ssx’,o_DEF]>>
  disch_then $ drule_at Any>>
  simp[o_DEF]>>
  pop_assum kall_tac>> (* ssx.compile_oracle *)

  ‘code_rel (arch_wordsize mc.target.config.ISA) jump off sp mprog ssx.code’
    by (
    simp[stack_removeProofTheory.code_rel_def]>>
    gs[Abbr ‘ssx’, Abbr ‘mprog’]>>
    gs[lookup_fromAList,domain_fromAList]>>
    gs[stack_removeTheory.compile_def]>>
    gs[stack_removeProofTheory.prog_comp_eta]>>
    reverse conj_asm1_tac
    >- (
      simp[stack_removeTheory.init_stubs_def]>>
      rewrite_tac[Once UNION_COMM]>>
      gs[MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
      ‘set (MAP (λ(p1,p2). p1) (compile (arch_wordsize mc.target.config.ISA) c.data_conf (compile p))) =
       set (MAP FST (compile (arch_wordsize mc.target.config.ISA) c.data_conf (compile p)))’
        by (
        gs[LIST_TO_SET_MAP]>>
        irule IMAGE_CONG>>rw[]>>pairarg_tac>>gs[])>>
      gs[])>>
    ntac 3 strip_tac>>
    conj_tac >- (
      qpat_x_assum ‘good_code _ p’ mp_tac>>
      simp[stack_to_labProofTheory.good_code_def]>>
      strip_tac>>
      gs[Once (GSYM stack_rawcallProofTheory.stack_rawcall_reg_bound)]>>
      drule stack_allocProofTheory.stack_alloc_reg_bound>>
      disch_then $ qspecl_then [‘compile p’,‘c.data_conf’] assume_tac>>
      gs[EVERY_MEM]>>
      pop_assum irule>>
      drule ALOOKUP_MEM>>strip_tac>>
      gs[MEM_MAP]>>
      pop_assum $ irule_at Any>>gs[])>>
    irule EQ_TRANS>>
    irule_at Any (ALOOKUP_prefix |> BODY_CONJUNCTS |> tl |> hd)>>
    reverse conj_asm2_tac>-gs[ALOOKUP_MAP]>>
    gs[stack_removeTheory.init_stubs_def]>>
    mp_tac (GEN_ALL (INST_TYPE [alpha |-> ``:64``]
      pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min))>>
    disch_then $ qspecl_then [‘wprog0’,‘pan_code’, ‘mc.target.config.ISA’] mp_tac>>
    impl_tac>- gs[Abbr ‘wprog0’]>>
    simp[GSYM EVERY_MAP]>>
    qpat_assum ‘MAP FST wprog = MAP FST _’ (fn h => PURE_REWRITE_TAC[GSYM h])>>

    drule word_to_stack_compile_FST>>
    gs[wordLangTheory.raise_stub_location_def,
       wordLangTheory.store_consts_stub_location_def]>>
    gs[backend_commonTheory.word_num_stubs_def]>>
    gs[backend_commonTheory.stack_num_stubs_def]>>
    strip_tac>>
    strip_tac>>
    gs[ALOOKUP_MAP]>>

    gs[stack_allocTheory.compile_def]>>
    gs[stack_rawcallTheory.compile_def]>>
    gs[ALOOKUP_APPEND]>>
    Cases_on ‘ALOOKUP (stubs (arch_wordsize mc.target.config.ISA) c.data_conf) n’>>
    gs[stack_allocTheory.stubs_def,
       stackLangTheory.gc_stub_location_def,
       backend_commonTheory.stack_num_stubs_def]>>

    gs[MAP_MAP_o,stack_allocTheory.prog_comp_def,o_DEF,LAMBDA_PROD]>>
    drule ALOOKUP_MEM>>gs[MEM_MAP]>>
    strip_tac>>
    pairarg_tac>>gs[]>>
    ‘MEM p1 (MAP FST p)’
      by (gs[MEM_MAP]>>first_assum $ irule_at (Pos last)>>gs[])>>gs[]>>
    gs[EVERY_MEM]>>
    first_x_assum $ qspec_then ‘p1’ assume_tac>>gs[])>>
  disch_then $ drule_at Any>>
  ‘init_code_pre (arch_wordsize mc.target.config.ISA) sp bitmaps data_sp ssx’
    by
    (simp[stack_removeProofTheory.init_code_pre_def]>>
     gs[stack_to_labProofTheory.memory_assumption_def]>>
     gs[Abbr ‘ssx’]>>
     gs[FLOOKUP_MAP_KEYS_LINV]>>
     MAP_EVERY qexists_tac [‘ptr2’, ‘ptr3’, ‘ptr4’, ‘bitmap_ptr'’]>>
     gs[]>>
     gs[flookup_fupdate_list]>>
     gs[REVERSE_DEF, ALOOKUP_APPEND]>>
     gs[]>>
     conj_tac >- simp[domain_fromAList, stack_removeTheory.compile_def,
                      stack_removeTheory.init_stubs_def]>>
     conj_tac >-
      (qpat_x_assum ‘MEM (_ _ sp) _’ $ irule_at Any>>
       simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
       gs[BIJ_DEF]>>metis_tac[])>>
     conj_tac >-
      (qpat_x_assum ‘MEM (_ _ (_+1)) _’ $ irule_at Any>>
       simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
       gs[BIJ_DEF]>>metis_tac[])>>
     (qpat_x_assum ‘MEM (_ _ (_+2)) _’ $ irule_at Any>>
      simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
      gs[BIJ_DEF]>>metis_tac[]))>>
  disch_then $ drule_at Any>>
  disch_then $ drule_at Any>>
  disch_then $ qspec_then ‘gck’ assume_tac>>gs[]>>

  ‘(w2n:64 word -> num) bytes_in_word = dimindex (:64) DIV 8’
    by fs[good_dimindex_def,bytes_in_word_def,dimword_def]>>
  ‘sss.regs ' (sp + 2) = Word (s.base_addr) ∧
   sss.regs ' (sp + 1) = Word (mc.target.get_reg ms mc.ptr2_reg
                               + 48w * bytes_in_word:64 word) ∧

   mc.target.get_reg ms mc.ptr2_reg = w3 ∧
   mc.target.get_reg ms mc.len2_reg = w4 ∧
   sss.sh_mdomain = sdm ∩ byte_aligned ∧
   t.regs mc.len_reg = w2 ∧
   t.regs mc.len2_reg = w4’
    by (
    gs[Abbr ‘ssx’, Abbr ‘labst’]>>
    fs[lab_to_targetProofTheory.make_init_def]>>

    gs[stack_removeProofTheory.init_prop_def]>>

    qpat_x_assum ‘init_reduce _ _ _ _ _ _ _ _ _ _ = x'’ (assume_tac o GSYM)>>fs[]>>
    fs[stack_removeProofTheory.init_reduce_def]>>

    gs[FLOOKUP_MAP_KEYS_LINV]>>
    gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>

    ‘store_init (is_gen_gc c.data_conf.gc_kind) sp CurrHeap =
     (INR (sp + 2) :int + num)’
      by gs[stack_removeTheory.store_init_def, APPLY_UPDATE_LIST_ALOOKUP]>>
    gs[]>>

    ‘ALL_DISTINCT
     (MAP FST (MAP (λn. case
                        store_init (is_gen_gc c.data_conf.gc_kind) sp n
                        of
                          INL w => (n,Word (i2w w))
                        | INR i => (n,sss.regs ' i)) store_list))’
      by (rewrite_tac[stack_removeTheory.store_list_def,
                      stack_removeTheory.store_init_def,
                      APPLY_UPDATE_LIST_ALOOKUP]>>
          gs[APPLY_UPDATE_LIST_ALOOKUP])>>

    gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>
    gs[alookup_distinct_reverse]>>

    gs[stack_removeTheory.store_list_def,
       stack_removeTheory.store_init_def,
       APPLY_UPDATE_LIST_ALOOKUP]>>

    (* need target_state_rel *)
    gs[targetSemTheory.good_init_state_def]>>
    gs[asmPropsTheory.target_state_rel_def]>>

    qpat_assum ‘∀i. _ ⇒ mc.target.get_reg ms _ = t.regs _’ assume_tac>>
    first_x_assum $ qspec_then ‘mc.len_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    strip_tac>>gs[]>>

    qpat_x_assum ‘FLOOKUP sss.regs (sp + 2) = SOME _’ mp_tac>>
    qpat_x_assum ‘sss.regs ' _ = Word curr’ mp_tac>>
    simp[FLOOKUP_DEF]>>ntac 2 strip_tac>>
    gs[wordSemTheory.theWord_def]>>
    (* base_addr done *)

    gs[stack_removeProofTheory.state_rel_def]>>
    Cases_on ‘FLOOKUP sss.regs (sp + 1)’>>gs[]>>
    rename1 ‘FLOOKUP _ (sp + 1) = SOME xxx’>>Cases_on ‘xxx’>>gs[]>>
    gs[flookup_thm]>>
    gs[wordSemTheory.theWord_def]>>
    gs[FLOOKUP_MAP_KEYS_LINV]>>
    gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>
    gs[wordSemTheory.theWord_def]>>
    qpat_assum ‘∀i. _ ⇒ mc.target.get_reg ms _ = t.regs _’ assume_tac>>
    first_assum $ qspec_then ‘mc.len_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    first_assum $ qspec_then ‘mc.ptr2_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    first_x_assum $ qspec_then ‘mc.len2_reg’ mp_tac>>
    impl_tac>-fs[asmTheory.reg_ok_def]>>
    ntac 2 strip_tac>>gs[]>>
    ‘(w3 + -1w * s.base_addr) ⋙ (backend_common$word_shift (dimindex (:64)) + 1) ≪ (backend_common$word_shift (dimindex (:64)) + 1)
     = w3 + -1w * s.base_addr’
      by (irule data_to_word_gcProofTheory.lsr_lsl>>gs[])>>
    gs[backendProofTheory.heap_regs_def]>>
    qpat_x_assum ‘w2 = _’ $ assume_tac o GSYM>>fs[])>>
  (* memory domain done *)

  (* memory shift *)
  qpat_x_assum ‘FLOOKUP sss.regs (sp + 2) = _’ mp_tac>>
  gs[flookup_thm]>>strip_tac>>gs[]>>
  ‘(w3 + -1w * s.base_addr) ⋙ (backend_common$word_shift (dimindex (:64)) + 1) ≪ (backend_common$word_shift (dimindex (:64)) + 1)
   = w3 + -1w * s.base_addr’
    by (irule data_to_word_gcProofTheory.lsr_lsl>>gs[])>>
  gs[]>>

  ‘w2n (-1w * w2 + w3 + bytes_in_word * n2w (LENGTH store_list)) DIV
   (dimindex (:64) DIV 8)  − LENGTH store_list =
   w2n (-1w * w2 + w3) DIV (dimindex (:64) DIV 8)’
    by
    (simp[SUB_RIGHT_EQ]>>
     irule OR_INTRO_THM1>>
     irule EQ_TRANS>>
     irule_at Any ADD_DIV_ADD_DIV>>
     ‘0 < dimindex (:64) DIV 8’ by gs[good_dimindex_def]>>fs[]>>
     ‘(LENGTH store_list) * (dimindex (:64) DIV 8)
      = w2n (bytes_in_word:64 word * n2w (LENGTH store_list))’
       by fs[good_dimindex_def,bytes_in_word_def,dimword_def,
             word_mul_def,stack_removeTheory.store_list_def]>>
     pop_assum (fn h => rewrite_tac[h])>>

     rewrite_tac[Once word_add_def]>>
     rewrite_tac[w2n_n2w]>>
     ‘w2n (w3 − w2) + w2n (bytes_in_word:64 word * n2w (LENGTH store_list)) < dimword (:64)’
       by (irule LESS_EQ_LESS_TRANS>>
           qexists_tac ‘w2n w4’>>
           simp[w2n_lt]>>
           ‘w2n (-1w * w2 + w3) ≤ w2n w4 - w2n (bytes_in_word:64 word * n2w (LENGTH store_list))’
             by (irule LESS_EQ_TRANS>>
                 qexists_tac ‘w2n (w4 + -1w * (bytes_in_word:64 word * n2w max_stack_alloc))’>>
                 rewrite_tac[Once WORD_ADD_COMM]>>
                 rewrite_tac[Once (GSYM WORD_NEG_MUL)]>>
                 rewrite_tac[GSYM word_sub_def]>>
                 ‘w3 - w2  <₊ w4 + -1w * (bytes_in_word * n2w max_stack_alloc)’
                   by (irule WORD_LOWER_LOWER_EQ_TRANS>>
                       last_assum $ irule_at Any>>
                       simp[]>>
                       rewrite_tac[Once WORD_ADD_LEFT_LO2]>>
                       conj_tac >-
                        (rewrite_tac[GSYM (cj 1 WORD_LO_word_0)]>>
                         irule WORD_LOWER_EQ_LOWER_TRANS>>
                         last_assum $ irule_at Any>>simp[])>>
                       irule OR_INTRO_THM1>>
                       rewrite_tac[GSYM WORD_NEG_MUL]>>
                       rewrite_tac[WORD_NEG_NEG]>>
                       simp[]>>
                       rewrite_tac[GSYM (cj 1 WORD_LO_word_0)]>>simp[])>>
                 drule (iffLR WORD_LO)>>strip_tac>>
                 drule LESS_IMP_LESS_OR_EQ>>strip_tac>>
                 fs[]>>
                 rewrite_tac[Once word_add_def]>>
                 rewrite_tac[w2n_n2w]>>
                 rewrite_tac[Once word_mul_def]>>
                 simp[w2n_minus1]>>
                 simp[LEFT_SUB_DISTRIB]>>
                 ‘w2n (bytes_in_word:64 word * n2w max_stack_alloc) ≤
                  dimword (:64) * w2n (bytes_in_word:64 word * n2w max_stack_alloc)’
                   by fs[good_dimindex_def,bytes_in_word_def,dimword_def,
                         stack_removeTheory.max_stack_alloc_def]>>
                 simp[GSYM LESS_EQ_ADD_SUB]>>
                 rewrite_tac[Once ADD_COMM]>>
                 ‘w2n (bytes_in_word:64 word * n2w max_stack_alloc) ≤ w2n w4’
                   by (
                   ‘1024w * bytes_in_word:64 word ≤₊ w4’
                      by (irule WORD_LOWER_EQ_TRANS>>
                          first_assum $ irule_at Any>>
                          rewrite_tac[WORD_ADD_LEFT_LS2]>>
                          irule OR_INTRO_THM2>>
                          qpat_assum ‘w2 ≤₊ w4’ $
                                     assume_tac o REWRITE_RULE[WORD_LOWER_OR_EQ]>>
                          gs[]>>
                          strip_tac>>gs[])>>
                   drule (iffLR WORD_LS)>>strip_tac>>
                   gs[good_dimindex_def,bytes_in_word_def,dimword_def,
                      stack_removeTheory.max_stack_alloc_def])>>
                 drule LESS_EQ_ADD_SUB>>
                 disch_then $ qspec_then
                            ‘dimword(:64) *
                             w2n (bytes_in_word:64 word * n2w max_stack_alloc)’
                            assume_tac>>
                 pop_assum (fn h => rewrite_tac[h])>>
                 rewrite_tac[Once MULT_COMM]>>
                 assume_tac ZERO_LT_dimword>>
                 simp[MOD_TIMES]>>
                 ‘w2n w4 - w2n (bytes_in_word:64 word * n2w max_stack_alloc)
                  < dimword(:64)’
                   by (simp[SUB_RIGHT_LESS]>>
                       irule LESS_TRANS>>
                       irule_at Any w2n_lt>>
                       fs[good_dimindex_def,bytes_in_word_def,dimword_def,
                          stack_removeTheory.max_stack_alloc_def])>>
                 simp[LESS_MOD]>>
                 fs[good_dimindex_def,bytes_in_word_def,dimword_def,
                    stack_removeTheory.max_stack_alloc_def,
                    stack_removeTheory.store_list_def]>>
                 qpat_x_assum `2040 <= w2n w4` mp_tac>>
                 qspec_then `w4` mp_tac w2n_lt>>
                 POP_ASSUM_LIST (K ALL_TAC)>>intLib.ARITH_TAC)>>
           fs[SUB_LEFT_LESS_EQ]>>
           fs[WORD_SUM_ZERO])>>
     rewrite_tac[Once (GSYM WORD_ADD_COMM)]>>
     rewrite_tac[GSYM WORD_NEG_MUL]>>
     rewrite_tac[GSYM word_sub_def]>>
     simp[LESS_MOD,bytes_in_word_def,stack_removeTheory.store_list_def]>>
     POP_ASSUM_LIST (K ALL_TAC)>>intLib.ARITH_TAC)>>
  gs[]>>

  (* pan_to_word *)

  fs [InitGlobals_location_eq_first_name]>>
  ‘wst0.code = fromAList (pan_to_word_compile_prog mc.target.config.ISA pan_code)’
    by gs[Abbr ‘wst0’, wordSemTheory.state_component_equality]>>

  drule_at Any (INST_TYPE [beta|-> “:num # lab_to_target$config”]
                pan_to_wordProofTheory.state_rel_imp_semantics)>>gs[]>>
  rpt $ disch_then $ drule_at Any>>gs[]>>
  simp[GSYM PULL_EXISTS] >>

  impl_tac
  >- (gs[Abbr ‘wst0’]>>
      gs[]>>

      gs[Abbr ‘wst’, Abbr ‘worac’,
         word_to_stackProofTheory.make_init_def]>>gvs[]>>
      fs[stack_removeProofTheory.init_reduce_def]>>
      gs[wordSemTheory.theWord_def]>>

      ‘store_init gck sp CurrHeap =
       (INR (sp + 2) :int + num)’
        by gs[stack_removeTheory.store_init_def, APPLY_UPDATE_LIST_ALOOKUP]>>
      gs[]>>

      ‘ALL_DISTINCT (MAP FST (MAP
                              (λn.
                                 case
                                 store_init gck sp n
                                 of
                                   INL w => (n,Word (i2w w))
                                 | INR i => (n,sss.regs ' i)) store_list))’
        by (rewrite_tac[stack_removeTheory.store_list_def,
                        stack_removeTheory.store_init_def,
                        APPLY_UPDATE_LIST_ALOOKUP]>>
            gs[APPLY_UPDATE_LIST_ALOOKUP])>>
      gs[flookup_fupdate_list]>>
      gs[ALOOKUP_APPEND]>>
      gs[alookup_distinct_reverse]>>
      fs[stack_removeTheory.store_list_def,
         stack_removeTheory.store_init_def,
         APPLY_UPDATE_LIST_ALOOKUP,
         wordSemTheory.theWord_def] >>
      conj_tac
      >- (rpt strip_tac >>
          irule EQ_TRANS >>
          first_x_assum $ irule_at (Pos last) >>
          simp[] >>
          irule EQ_TRANS >>
          irule_at (Pos hd) EQ_SYM >>
          irule_at (Pos hd) $ iffLR set_sepTheory.fun2set_eq >>
          first_assum $ irule_at $ Pos hd >>
          simp[] >>
          conj_tac
          >- (gs[stack_removeProofTheory.addresses_thm] >>
              irule_at Any EQ_REFL >>
              simp[]) >>
          gs[Abbr ‘ssx’, Abbr ‘labst’]>>
          rewrite_tac[lab_to_targetProofTheory.make_init_def]>>simp[]>>
          gs[wordSemTheory.theWord_def]>>
          gs[set_sepTheory.fun2set_eq]) >>
      conj_tac
      >- (rw[no_labels_def] >>
          irule_at Any EQ_TRANS >>
          irule_at (Pos hd) EQ_SYM >>
          irule_at (Pos hd) $ iffLR set_sepTheory.fun2set_eq >>
          first_assum $ irule_at $ Pos hd >>
          simp[] >>
          gs[Abbr ‘ssx’, Abbr ‘labst’]>>
          rewrite_tac[lab_to_targetProofTheory.make_init_def]>>simp[]>>
          gs[wordSemTheory.theWord_def]>>
          gs[set_sepTheory.fun2set_eq]>>
          qpat_x_assum ‘good_init_state _ _ _ _ _ _ _ _’ mp_tac >>
          simp[targetSemTheory.good_init_state_def] >>
          ‘byte_aligned a’
            by(gs[stack_removeProofTheory.addresses_thm] >>
               simp[bytes_in_word_def,
                    PURE_ONCE_REWRITE_RULE [WORD_ADD_COMM] byte_aligned_mult]) >>
          pop_assum mp_tac >>
          rpt $ pop_assum kall_tac >>
          metis_tac[byte_align_aligned]) >>
      conj_tac
      >- (rw[SET_EQ_SUBSET,SUBSET_DEF,stack_removeProofTheory.addresses_thm,
             addressTheory.WORD_EQ_ADD_CANCEL,WORD_EQ_ADD_RCANCEL]
          >- (simp[addressTheory.WORD_EQ_ADD_CANCEL] >>
              qmatch_goalsub_abbrev_tac ‘_ < www’ >>
              Cases_on ‘i < www’
              >- (disj1_tac >> irule_at Any EQ_REFL >> simp[]) >>
              disj2_tac >>
              simp[WORD_EQ_ADD_RCANCEL] >>
              qexists ‘i - www’ >>
              gs[Abbr ‘www’,NOT_LESS] >>
              gs[good_dimindex_def,bytes_in_word_def,word_mul_n2w,word_add_n2w] >>
              simp[REWRITE_RULE[wordsTheory.word_sub_def] addressTheory.word_arith_lemma2] >>
              ‘∀x. 32 * x DIV 8 = 4 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘4*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              ‘∀x. 64 * x DIV 8 = 8 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘8*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              PURE_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB,LT_MULT_LCANCEL] >>
              simp[SUB_LEFT_SUB] >>
              simp[LEFT_ADD_DISTRIB] >>
              match_mp_tac native_globals_split >> first_assum ACCEPT_TAC)
          >- (irule_at Any EQ_REFL >> simp[])
          >- (simp[WORD_EQ_ADD_RCANCEL] >>
              qexists ‘(w2n
                        (-1w * mc.target.get_reg ms mc.len_reg +
                         mc.target.get_reg ms mc.ptr2_reg) DIV (dimindex (:64) DIV 8)) + i -
                             SUM (MAP (size_of_sh_with_ctxt (THE (decs_stcnames [] pan_code))) (dec_shapes pan_code))
                      ’ >>
              simp[] >>
              gs[good_dimindex_def,bytes_in_word_def,word_mul_n2w,word_add_n2w] >>
              simp[REWRITE_RULE[wordsTheory.word_sub_def] addressTheory.word_arith_lemma2] >>
              ‘∀x. 32 * x DIV 8 = 4 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘4*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              ‘∀x. 64 * x DIV 8 = 8 * x’
                by(rpt $ pop_assum kall_tac >>
                   strip_tac >>
                   irule_at Any EQ_TRANS >>
                   irule_at (Pos last) $ Q.SPEC ‘8*x’ MULT_TO_DIV >>
                   qexists ‘8’ >>
                   intLib.COOPER_TAC) >>
              pop_assum $ simp o single >>
              PURE_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB,LT_MULT_LCANCEL] >>
              simp[SUB_LEFT_SUB] >>
              simp[LEFT_ADD_DISTRIB] >>
              match_mp_tac native_globals_join >> first_assum ACCEPT_TAC)) >>
      gvs[Abbr ‘sp’] >>
      gs[word_to_stackProofTheory.make_init_def]>>
      gs[Abbr ‘labst’,Abbr ‘ssx’] >>
      gs[stack_removeProofTheory.init_prop_def,flookup_fupdate_list] >>

      qpat_x_assum ‘(word_list_exists _ len * word_list_exists _ _) _’ mp_tac >>
      PURE_REWRITE_TAC[Once WORD_ADD_COMM] >>
      PURE_REWRITE_TAC[GSYM stack_removeProofTheory.word_list_exists_ADD] >>
      simp[] >>
      strip_tac >>
      drule word_list_exists_addresses >>
      impl_tac
      >- (simp[] >>
          gs[good_dimindex_def,dimword_def,DIV_LT_X] >>
          irule LESS_LESS_EQ_TRANS >>
          irule_at (Pos hd) w2n_lt >>
          simp[dimword_def]) >>
      ‘2w:64 word * (bytes_in_word * n2w len) = bytes_in_word * n2w(2*len)’
        by simp[GSYM word_mul_n2w] >>
      pop_assum SUBST_ALL_TAC >>
      disch_then $ simp o single >>
      simp[] >>
      PURE_REWRITE_TAC[WORD_EQ_ADD_LCANCEL,GSYM WORD_ADD_ASSOC] >>
      conj_tac
      >- (simp[bytes_in_word_def,word_mul_n2w] >> PURE_REWRITE_TAC[GSYM WORD_NEG_MUL] >>
          gs[good_dimindex_def] >>
          PURE_REWRITE_TAC[DECIDE “32:num = 8*4”,DECIDE “64:num = 8*8”,GSYM MULT_ASSOC] >>
          PURE_REWRITE_TAC[SIMP_RULE std_ss [] $ Q.SPEC ‘8’ MULT_DIV
                           |> PURE_ONCE_REWRITE_RULE[MULT_COMM]] >>
          simp[]) >>
      irule byte_aligned_add >>
      drule pan_globalsProofTheory.byte_aligned_bytes_in_word_mul >>
      simp[good_dimindex_div_mul,bytes_in_word_def,GSYM word_mul_n2w,
           Once bytes_in_word_def] >>
      strip_tac >>
      conj_tac >- (simp[alignmentTheory.byte_aligned_def,aligned_w2n,word_mul_def] >>
                   POP_ASSUM_LIST (K ALL_TAC) >> intLib.ARITH_TAC) >>
      irule byte_aligned_add >>
      conj_tac >- (simp[alignmentTheory.byte_aligned_def,aligned_w2n,word_mul_def] >>
                   POP_ASSUM_LIST (K ALL_TAC) >> intLib.ARITH_TAC) >>
      simp[])>>
  gs[]>>

  (* resource_limit implication *)
  strip_tac>>
  reverse conj_tac
  >- (strip_tac>>
      gs[semanticsPropsTheory.extend_with_resource_limit_def]>>
      once_rewrite_tac[GSYM UNION_ASSOC]>>
      simp[SUBSET_UNION])>>
  qpat_x_assum ‘_ = stack_max’ $ assume_tac o GSYM>>
  gs[wordSemTheory.word_lang_safe_for_space_def]>>
  pop_assum kall_tac>>
  rpt strip_tac>>
  drule word_depthProofTheory.max_depth_Call_NONE>>
  disch_then $ qspec_then ‘fromAList wprog’ assume_tac>>gs[]>>
  gs[option_lt_SOME]>>
  ‘res ≠ SOME Error’
    by (first_x_assum $ qspecl_then [‘t'’, ‘k’] assume_tac>>gs[])>>gs[]>>

  drule evaluate_stack_size_limit_const_panLang>>
  impl_tac >-
   (gs[Abbr ‘wst’,
       wordConvsTheory.no_mt_def,
       wordConvsTheory.no_alloc_def,
       wordConvsTheory.no_install_def]>>
    drule_all word_to_word_compile_no_install_no_alloc>>strip_tac>>
    gs[])>>
  strip_tac>>

  gs[backendProofTheory.read_limits_def]>>
  gs[stack_removeProofTheory.get_stack_heap_limit_def]>>
  gs[stack_removeProofTheory.get_stack_heap_limit'_def]>>
  gs[stack_removeProofTheory.get_stack_heap_limit''_def]>>
  gs[WORD_LO]>>
  ‘¬ (w2n (bytes_in_word:64 word * n2w max_heap) <
      w2n (w3 + -1w * s.base_addr))’
    by (gs[NOT_LESS]>>
        irule LESS_EQ_TRANS>>
        first_assum $ irule_at Any>>
        simp[word_mul_def])>>gs[]>>
  pop_assum $ kall_tac>>
  ‘(w3 + -1w * s.base_addr) ⋙ (backend_common$word_shift (dimindex (:64)) + 1) ≪ (backend_common$word_shift (dimindex (:64)) + 1) =
   w3 + -1w * s.base_addr’
    by (irule data_to_word_gcProofTheory.lsr_lsl>>gs[])>>gs[]>>
  pop_assum $ kall_tac>>

  qpat_x_assum ‘word_to_stack$compile _ _ _ = _’ mp_tac>>
  simp[word_to_stackTheory.compile_def]>>
  pairarg_tac>>gs[]>>
  strip_tac>>
  qpat_x_assum ‘_ = c''’ $ assume_tac o GSYM>>gs[]>>

  gs[Abbr ‘wst’, Abbr ‘worac’]>>
  gs[word_to_stackProofTheory.make_init_def]>>
  qpat_x_assum ‘_ = sst’ $ assume_tac o GSYM>>gs[]>>
  qpat_x_assum ‘init_reduce _ _ _ _ _ _ _ _ _ _ = x'’ $ assume_tac o GSYM>>gs[]>>
  gs[stack_removeProofTheory.init_reduce_def]>>
  gs[stack_removeProofTheory.LENGTH_read_mem]>>
  pop_assum kall_tac>>
  pop_assum kall_tac>>

  drule backendProofTheory.compile_word_to_stack_sfs_aux>>
  strip_tac>>

  qpat_x_assum ‘option_le _ _’ mp_tac>>
  simp[mapi_Alist]>>
  qmatch_goalsub_abbrev_tac ‘max_depth (fromAList (MAP f _)) _’>>
  ‘fromAList (MAP f (toAList (fromAList wprog))) =
   map (λ(arg_count,prog).
          FST
          (SND
           (compile_prog mc.target.config F prog arg_count
            (mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 5))
            (Nil,0)))) (fromAList (toAList (fromAList wprog)))’
    by (irule EQ_TRANS>>
        irule_at Any (GSYM map_fromAList)>>
        gs[Abbr ‘f’]>>gs[LAMBDA_PROD])>>
  gs[]>>
  simp[wf_fromAList,fromAList_toAList]>>
  pop_assum kall_tac>>
  simp[map_fromAList]>>gs[LAMBDA_PROD]>>
  strip_tac>>gs[wordSemTheory.stack_size_def]>>
  gs[data_to_wordProofTheory.option_le_SOME]>>
  qpat_x_assum ‘m' < _’ assume_tac>>
  gs[wordSemTheory.theWord_def]>>
  qpat_x_assum ‘w2n _ ≤ _ * max_heap’ assume_tac>>
  qpat_x_assum ‘aligned _ _’ assume_tac>>

  irule LESS_EQ_TRANS>>
  first_assum $ irule_at Any>>gs[]>>
  simp[LESS_EQ_IFF_LESS_SUC]>>
  irule LESS_LESS_EQ_TRANS>>
  first_assum $ irule_at Any>>
  rewrite_tac[LESS_OR_EQ]>>
  irule OR_INTRO_THM2>>simp[]>>
  qpat_x_assum ‘48w * _ = _ * _’ $ assume_tac>>
  ‘LENGTH store_list = 48’
  by simp[stack_removeTheory.store_list_def]>>
  fs[]>>

  ‘0 < dimindex (:64) DIV 8’ by fs[good_dimindex_def]>>
  qpat_x_assum ‘w3 ≤₊ w4 + _’ assume_tac>>
  qpat_x_assum ‘_ ≤ max_heap’ assume_tac>>
  qpat_x_assum ‘_ * max_heap < _’ assume_tac>>
  blastLib.BBLAST_TAC>>
  rewrite_tac[SUC_ONE_ADD]>>

  rewrite_tac[Once (GSYM WORD_ADD_ASSOC)]>>
  rewrite_tac[Once WORD_ADD_COMM]>>
  rewrite_tac[Once (GSYM word_sub_def)]>>
  ‘1024w * bytes_in_word:64 word ≤₊ w4’
    by (irule WORD_LOWER_EQ_TRANS>>
        first_assum $ irule_at Any>>
        rewrite_tac[WORD_ADD_LEFT_LS2]>>
        irule OR_INTRO_THM2>>
        qpat_assum ‘w2 ≤₊ w4’ $ assume_tac o REWRITE_RULE[WORD_LOWER_OR_EQ]>>
        gs[]>>
        strip_tac>>gs[])>>
  ‘49w * bytes_in_word:64 word <₊ w4’
  by (
    irule WORD_LOWER_LOWER_EQ_TRANS>>
    first_assum $ irule_at Any>>
    gs[WORD_LO,bytes_in_word_def,good_dimindex_def,dimword_def])>>
  ‘w3 ≤₊ w4 + -49w * bytes_in_word:64 word’
    by (irule WORD_LOWER_EQ_TRANS>>
        first_assum $ irule_at Any>>
        simp[stack_removeTheory.max_stack_alloc_def]>>
        qpat_x_assum `1024w * bytes_in_word <=+ w4` mp_tac>>
        qspec_then `w4` mp_tac w2n_lt>>
        POP_ASSUM_LIST (K ALL_TAC)>>
        simp[bytes_in_word_def,word_mul_def,word_add_def,WORD_LS]>>
        intLib.ARITH_TAC)>>
  fs[word_sub_w2n]>>
  ‘byte_aligned (w3 - w2)’
    by (simp[Once WORD_NEG_MUL]>>
        simp[byte_aligned_def]>>
        irule aligned_imp>>
        qexists_tac `backend_common$word_shift 64 + 1`>>
        fs[backend_commonTheory.word_shift_def])>>
  qpat_assum ‘byte_aligned (w3 - _)’ $ assume_tac o REWRITE_RULE[byte_aligned_def]>>
  qpat_assum ‘byte_aligned w2’ $ assume_tac o REWRITE_RULE[byte_aligned_def]>>
  drule_all (iffLR (aligned_add_sub |> cj 2))>>strip_tac>>
  fs[GSYM byte_aligned_def]>>
  drule_all (byte_aligned_MOD |> REWRITE_RULE[SPECIFICATION])>>strip_tac>>
  gs[MOD_EQ_0_DIVISOR]>>
  simp[Q.SPECL [‘dimindex (:64) DIV 8’, ‘0’] DIV_MULT |> SIMP_RULE (std_ss)[]]>>

  drule (iffLR WORD_LS)>>strip_tac>>
  gs[]>>
  pop_assum $ assume_tac o ONCE_REWRITE_RULE[MULT_COMM]>>
  ONCE_REWRITE_TAC[MULT_COMM]>>
  qpat_x_assum `d * 8 <= w2n (w4 + _)` mp_tac>>
  qpat_x_assum `w2n w3 = 8 * d` mp_tac>>
  qpat_x_assum `1024w * bytes_in_word <=+ w4` mp_tac>>
  qpat_x_assum `byte_aligned w4` mp_tac>>
  qspec_then `w4` mp_tac w2n_lt>>
  qspec_then `w3` mp_tac w2n_lt>>
  POP_ASSUM_LIST (K ALL_TAC)>>
  simp[bytes_in_word_def,alignmentTheory.byte_aligned_def,aligned_w2n,
       word_mul_def,word_add_def,WORD_LS]>>
  intLib.ARITH_TAC

QED

val _ = check_thm challenge_pan_to_target_compile_semantics;

val _ = if null(hyp challenge_pan_to_target_compile_semantics) then ()
  else failwith "challenge Pancake assumptions";
