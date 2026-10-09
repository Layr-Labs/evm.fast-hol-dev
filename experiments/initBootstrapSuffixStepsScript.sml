(* Actual instruction execution of the fixed runtime-initialization suffix. *)
Theory initBootstrapSuffixSteps
Ancestors initBootstrapCopyExecution initBootstrapSuffix initBootstrapFrame
Libs preamble wordsLib cv_transLib
open asmSemTheory asmPropsTheory wordsTheory initBootstrapTheory
  initBootstrapLoopTheory initBootstrapMemoryTheory initBootstrapStoresTheory
  initBootstrapStepTheory initBootstrapPrefixStepsTheory initBootstrapExecutionTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val instructions = fst (listSyntax.dest_list (rhs (concl bootstrap_suffix)));
val blocks = fst (listSyntax.dest_list
  (rhs (concl (EVAL ``DROP 8 bootstrapBlocks``))));
val pcs = map (fst o pairSyntax.dest_pair) blocks;
val enc_lengths = map (fn instruction => cv_eval ``LENGTH (riscv_enc ^instruction)``) instructions;
val membership = map (fn block => EVAL ``MEM ^block bootstrapBlocks``) blocks;
val store_consts = save_thm ("store_consts",
  ISPECL [``asm$Inst (asm$Mem asm$Store rn (asm$Addr rb off))``,
    ``0w:word64``,``s:64 asm_state``] asm_consts
  |> PURE_REWRITE_RULE [asm_def,inst_def,mem_op_def,upd_pc_def]
  |> SIMP_RULE (srw_ss()) []);
val step_simps = enc_lengths @ [bootAfter_def,asm_def,inst_def,
  mem_op_def,arith_upd_def,binop_upd_def,word_shift_def,assert_def,
  reg_imm_def,read_reg_def,upd_pc_def,upd_reg_def,jump_to_offset_def,
  store_register_frame,store_consts,APPLY_UPDATE_THM];
val state_rules = List.concat (map (fn instruction =>
  map (SIMP_CONV (srw_ss()) step_simps)
    [``(bootAfter ^instruction (s:64 asm_state)).regs``,
     ``(bootAfter ^instruction (s:64 asm_state)).pc``,
     ``(bootAfter ^instruction (s:64 asm_state)).be``,
     ``(bootAfter ^instruction (s:64 asm_state)).mem_domain``,
     ``(bootAfter ^instruction (s:64 asm_state)).lr``,
     ``(bootAfter ^instruction (s:64 asm_state)).align``]) instructions);
val memory_rules = map (fn instruction =>
  DISCH_ALL (SIMP_CONV (srw_ss())
    (ASSUME ``~(s:64 asm_state).be`` :: store_memory :: addr_def :: step_simps)
    ``(bootAfter ^instruction (s:64 asm_state)).mem``)) instructions;
val failure_rules = map (fn instruction =>
  DISCH_ALL (SIMP_CONV (srw_ss())
    (ASSUME ``~(s:64 asm_state).be`` :: mem_store_def ::
      write_word_failed :: write_word_frame :: addr_def :: LET_DEF :: step_simps)
    ``(bootAfter ^instruction (s:64 asm_state)).failed``)) instructions;
Theorem suffix_store_below:
  w2n a < bootDataRam /\ bootDataRam <= address /\ address + 8 < 2**64 ==>
  littleStore 8 (n2w address) w bytesAt a = bytesAt a
Proof
  strip_tac >> irule little_store_below >>
  fs [] >> decide_tac
QED
fun suffix_step_tac pc goal =
  (print ("Checking suffix instruction at " ^ term_to_string pc ^ "\n");
  (irule (INST [``pc:num`` |-> pc] bootstrap_asm_step) >>
  fs (membership @ state_rules @ failure_rules @ memory_rules @
    [bootstrapRomInvariant_def,integer_wordTheory.i2w_def,aligned_w2n,
     APPLY_UPDATE_THM,bootDataRam_def,suffix_store_below]) >>
  TRY (qexists_tac `input`) >> rpt strip_tac >>
  fs [suffix_store_below,bootDataRam_def] >> gvs [] >>
  TRY (qexists_tac `input`) >> simp [] >>
  (fn g => (print_term (snd g); print "\n"; ALL_TAC g))) goal);
Theorem bootstrap_suffix_steps:
  bootstrapRomInvariant input s /\ s.pc = 0x8000002cw /\
  s.lr = 1 /\ ~s.be /\ s.align = 2 /\ ~s.failed /\
  (!j. j < 24 ==> n2w (0xa0020000+j) IN s.mem_domain) /\
  (!j. j < 40 ==> n2w (0xa1000000+j) IN s.mem_domain) ==>
  bootSteps bootstrapSuffix s
Proof
  strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV))) >>
  simp [bootstrap_suffix,bootSteps_def] >>
  MAP_EVERY (fn pc => conj_tac >- suffix_step_tac pc) (List.take(pcs,length pcs-1)) >>
  suffix_step_tac (List.last pcs)
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "suffix execution assumptions")
  (bootstrap_suffix_steps :: suffix_store_below :: store_consts ::
   enc_lengths @ membership @ state_rules @ memory_rules @ failure_rules);
