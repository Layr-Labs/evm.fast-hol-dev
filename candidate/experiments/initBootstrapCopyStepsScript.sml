(* The five encoded instructions of one copy-loop iteration are valid steps. *)
Theory initBootstrapCopySteps
Ancestors initBootstrapExecution
Libs preamble wordsLib cv_transLib
open asmSemTheory asmTheory asmPropsTheory wordsTheory
  initBootstrapTheory initBootstrapLoopTheory initBootstrapMemoryTheory
  initBootstrapStepTheory initBootstrapPrefixStepsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem copy_load_consts:
  (mem_load 8 28 (Addr 5 0) (s:64 asm_state)).lr = s.lr /\
  (mem_load 8 28 (Addr 5 0) s).align = s.align /\
  (mem_load 8 28 (Addr 5 0) s).be = s.be /\
  (mem_load 8 28 (Addr 5 0) s).mem_domain = s.mem_domain
Proof
  mp_tac (ISPECL [``asm$Inst (asm$Mem asm$Load 28 (asm$Addr 5 0))``,``0w:word64``,
    ``s:64 asm_state``] asm_consts
    |> PURE_REWRITE_RULE [asm_def,inst_def,mem_op_def,upd_pc_def]
    |> SIMP_RULE (srw_ss()) []) >> metis_tac []
QED
Theorem copy_store_consts:
  (mem_store 8 28 (Addr 6 0) (s:64 asm_state)).lr = s.lr /\
  (mem_store 8 28 (Addr 6 0) s).align = s.align /\
  (mem_store 8 28 (Addr 6 0) s).be = s.be /\
  (mem_store 8 28 (Addr 6 0) s).mem_domain = s.mem_domain
Proof
  mp_tac (ISPECL [``asm$Inst (asm$Mem asm$Store 28 (asm$Addr 6 0))``,``0w:word64``,
    ``s:64 asm_state``] asm_consts
    |> PURE_REWRITE_RULE [asm_def,inst_def,mem_op_def,upd_pc_def]
    |> SIMP_RULE (srw_ss()) []) >> metis_tac []
QED
Theorem copy_word_consts:
  (copyWord s).lr = s.lr /\ (copyWord s).align = s.align /\
  (copyWord s).be = s.be /\ (copyWord s).mem_domain = s.mem_domain
Proof
  simp [copyWord_def,copy_store_consts,copy_load_consts]
QED
Theorem copy_load_success:
  ~(s:64 asm_state).be /\ ~s.failed /\ aligned 3 (s.regs 5) /\
  (!j. j < 8 ==> s.regs 5 + n2w j IN s.mem_domain) ==>
  ~(mem_load 8 28 (Addr 5 0) s).failed
Proof
  strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV))) >>
  fs [load_failed,addr_def,read_reg_def,read_word_failed,
    integer_wordTheory.i2w_0,WORD_ADD_ASSOC]
QED
Theorem copy_load_preserves_rom:
  bootstrapRomInvariant input s ==>
  bootstrapRomInvariant input (mem_load 8 28 (Addr 5 0) s)
Proof
  simp [bootstrapRomInvariant_def,load_frame]
QED
Theorem copy_word_preserves_rom:
  bootstrapRomInvariant input s /\ ~s.be /\
  (!j. j < 8 ==> bootDataRam <= w2n (s.regs 6 + n2w j)) ==>
  bootstrapRomInvariant input (copyWord s)
Proof
  rw [bootstrapRomInvariant_def,copyWord_frame] >>
  `(copyWord s).mem a = s.mem a` by
    (irule copyWord_outside >> fs [] >> rpt strip_tac >>
     first_x_assum (qspec_then `j` mp_tac) >> fs [] >> decide_tac) >>
  metis_tac []
QED
val instructions = fst (listSyntax.dest_list (rhs (concl copy_loop_body)));
val enc_lengths = map (fn instruction => cv_eval ``LENGTH (riscv_enc ^instruction)``) instructions;
val membership = map (fn (pc,instruction) => EVAL
  ``MEM (^pc,^instruction) bootstrapBlocks``)
  (ListPair.zip (map numSyntax.term_of_int
    [2147483672,2147483676,2147483680,2147483684,2147483688],instructions));
val step_simps = membership @ enc_lengths @
  [bootAfter_def,asm_def,inst_def,mem_op_def,upd_pc_def,upd_reg_def,
   arith_upd_def,binop_upd_def,reg_imm_def,read_reg_def,
   jump_to_offset_def,word_cmp_def,load_pc,store_pc,GSYM copyWord_def,
   copy_load_consts,copy_word_consts,load_frame,copyWord_frame,
   load_registers,APPLY_UPDATE_THM,WORD_ADD_ASSOC,
   EVAL ``i2w (8:int):word64``, EVAL ``i2w (-16:int):word64``];
fun copy_step pc =
  irule (Q.INST [`pc` |-> pc] bootstrap_asm_step) >>
  fs step_simps >>
  fs [bootstrapRomInvariant_def,load_frame,copyWord_frame,COND_RAND] >> metis_tac [];
Theorem copy_loop_steps:
  bootstrapRomInvariant input s /\ s.pc = 0x80000018w /\
  s.lr = 1 /\ ~s.be /\ s.align = 2 /\ ~s.failed /\
  aligned 3 (s.regs 5) /\ aligned 3 (s.regs 6) /\
  (!j. j < 8 ==> s.regs 5 + n2w j IN s.mem_domain) /\
  (!j. j < 8 ==> s.regs 6 + n2w j IN s.mem_domain) /\
  (!j. j < 8 ==> bootDataRam <= w2n (s.regs 6 + n2w j)) ==>
  bootSteps copyLoopBody s
Proof
  strip_tac >> imp_res_tac copy_load_success >> imp_res_tac copyWord_success >>
  imp_res_tac copy_load_preserves_rom >> imp_res_tac copy_word_preserves_rom >>
  simp [copy_loop_body,bootSteps_def] >> rpt conj_tac
  >- copy_step `0x80000018`
  >- copy_step `0x8000001c`
  >- copy_step `0x80000020`
  >- copy_step `0x80000024` >>
  copy_step `0x80000028`
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "copy-loop steps assumptions")
  ([copy_load_consts,copy_store_consts,copy_word_consts,copy_load_success,
    copy_load_preserves_rom,copy_word_preserves_rom,copy_loop_steps] @
   enc_lengths @ membership);
