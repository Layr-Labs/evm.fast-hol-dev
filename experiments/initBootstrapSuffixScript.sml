(* The actual post-copy instructions establish native entry registers. *)
Theory initBootstrapSuffix
Ancestors initBootstrapStartup initBootstrapStores
Libs preamble wordsLib cv_transLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapLoopTheory
  initBootstrapMemoryTheory;
Theorem store_register_frame:
  (mem_store n rn a (s:64 asm_state)).regs = s.regs /\
  (mem_store n rn a s).pc = s.pc /\
  (mem_store n rn a s).be = s.be /\
  (mem_store n rn a s).mem_domain = s.mem_domain
Proof
  simp [mem_store_def,assert_def,write_word_frame]
QED
Definition bootstrapSuffix_def:
  bootstrapSuffix = MAP SND (DROP 8 bootstrapBlocks)
End
val suffix = save_thm ("bootstrap_suffix", EVAL ``bootstrapSuffix``);
val instructions = fst (listSyntax.dest_list (rhs (concl suffix)));
val enc_lengths = map (fn instr => cv_eval ``LENGTH (riscv_enc ^instr)``) instructions;
(* Reduce one instruction at a time, keeping its incoming state symbolic.
   Expanding the whole instruction list duplicates nested state expressions. *)
val step_simps = enc_lengths @ [bootAfter_def,asm_def,inst_def,
  mem_op_def,arith_upd_def,binop_upd_def,word_shift_def,assert_def,
  reg_imm_def,read_reg_def,upd_pc_def,upd_reg_def,jump_to_offset_def,
  store_register_frame,APPLY_UPDATE_THM];
val state_rules = List.concat (map (fn instr =>
  map (SIMP_CONV (srw_ss()) step_simps)
    [``(bootAfter ^instr (s:64 asm_state)).regs``,
     ``(bootAfter ^instr (s:64 asm_state)).pc``,
     ``(bootAfter ^instr (s:64 asm_state)).be``,
     ``(bootAfter ^instr (s:64 asm_state)).mem_domain``]) instructions);
val memory_rules = map (fn instr =>
  DISCH_ALL (SIMP_CONV (srw_ss())
    (ASSUME ``~(s:64 asm_state).be`` :: store_memory :: addr_def :: step_simps)
    ``(bootAfter ^instr (s:64 asm_state)).mem``)) instructions;
val failure_rules = map (fn instr =>
  DISCH_ALL (SIMP_CONV (srw_ss())
    (ASSUME ``~(s:64 asm_state).be`` :: mem_store_def ::
      write_word_failed :: write_word_frame :: addr_def :: LET_DEF :: step_simps)
    ``(bootAfter ^instr (s:64 asm_state)).failed``)) instructions;
Definition bootstrapStoredBytes_def:
  bootstrapStoredBytes bytesAt =
    littleStore 8 0xa1000020w 0x800de000w
    (littleStore 8 0xa1000018w 0x800ddd08w
    (littleStore 8 0xa1000010w 0xa0029048w
    (littleStore 8 0xa1000008w 0xa0029048w
    (littleStore 8 0xa1000000w 0xa0020018w
    (littleStore 8 0xa0020010w 0x7e0000000w
    (littleStore 8 0xa0020008w 0x7df000000w
    (littleStore 8 0xa0020000w 0xa1000000w bytesAt)))))))
End
Theorem bootstrap_suffix_memory:
  s.pc = 0x8000002cw /\ ~s.be ==>
  (bootRun bootstrapSuffix s).mem = bootstrapStoredBytes s.mem
Proof
  strip_tac >>
  simp (state_rules @ memory_rules @ [suffix,bootRun_def,APPLY_UPDATE_THM,
    bootstrapStoredBytes_def,integer_wordTheory.i2w_def]) >> EVAL_TAC
QED
Theorem bootstrap_suffix_registers:
  s.pc = 0x8000002cw ==>
  (bootRun bootstrapSuffix s).regs 10 = n2w baselineNativePc /\
  (bootRun bootstrapSuffix s).regs 11 = 0xa1000000w /\
  (bootRun bootstrapSuffix s).regs 12 = 0x7df000000w /\
  (bootRun bootstrapSuffix s).regs 13 = 0x7e0000000w /\
  (bootRun bootstrapSuffix s).pc = n2w baselineNativePc /\
  (bootRun bootstrapSuffix s).be = s.be /\
  (bootRun bootstrapSuffix s).mem_domain = s.mem_domain
Proof
  strip_tac >>
  simp (state_rules @ [suffix,bootRun_def,APPLY_UPDATE_THM,baselineNativePc_def]) >>
  EVAL_TAC
QED
Theorem bootstrap_suffix_success:
  s.pc = 0x8000002cw /\ ~s.be /\ ~s.failed /\
  (!j. j < 24 ==> n2w (0xa0020000+j) IN s.mem_domain) /\
  (!j. j < 40 ==> n2w (0xa1000000+j) IN s.mem_domain) ==>
  ~(bootRun bootstrapSuffix s).failed
Proof
  strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV))) >>
  simp (state_rules @ failure_rules @ [suffix,bootRun_def,APPLY_UPDATE_THM,
    integer_wordTheory.i2w_def,aligned_w2n]) >> EVAL_TAC
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "suffix assumptions")
  (store_register_frame :: bootstrap_suffix_registers :: bootstrap_suffix_memory :: bootstrap_suffix_success ::
   (enc_lengths @ state_rules @ memory_rules @ failure_rules));
