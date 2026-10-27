(* One iteration of the copy loop, using the actual encoded bootstrap
   instructions. Memory admission is proved separately from this state update. *)
Theory initBootstrapLoop
Ancestors initBootstrap initBootstrapMemory
Libs preamble wordsLib cv_transLib
open asmSemTheory asmTheory wordsTheory;
Definition copyLoopBody_def:
  copyLoopBody = MAP SND (TAKE 5 (DROP 3 bootstrapBlocks))
End
Theorem copy_loop_body:
  copyLoopBody = [asm$Inst (asm$Mem asm$Load 28 (asm$Addr 5 0));
    asm$Inst (asm$Mem asm$Store 28 (asm$Addr 6 0));
    asm$Inst (asm$Arith (asm$Binop asm$Add 5 5 (asm$Imm 8)));
    asm$Inst (asm$Arith (asm$Binop asm$Add 6 6 (asm$Imm 8)));
    asm$JumpCmp asm$Lower 6 (asm$Reg 7) (-16)]
Proof
  EVAL_TAC
QED
Definition bootAfter_def:
  bootAfter instr (s:64 asm_state) =
    asmSem$asm instr (s.pc + n2w (LENGTH (riscv_enc instr))) s
End
Definition bootRun_def:
  bootRun [] s = s /\
  bootRun (instr::rest) s = bootRun rest (bootAfter instr s)
End
val instructions = fst (listSyntax.dest_list (rhs (concl copy_loop_body)));
val enc_lengths = map (fn instr => cv_eval ``LENGTH (riscv_enc ^instr)``) instructions;
val _ = List.app (fn th => ignore (check_thm th)) enc_lengths;
Theorem copy_loop_effect:
  (bootRun copyLoopBody s).mem = (copyWord s).mem /\
  (bootRun copyLoopBody s).regs 5 = s.regs 5 + 8w /\
  (bootRun copyLoopBody s).regs 6 = s.regs 6 + 8w /\
  (bootRun copyLoopBody s).regs 7 = s.regs 7 /\
  (bootRun copyLoopBody s).failed = (copyWord s).failed /\
  (bootRun copyLoopBody s).be = s.be /\
  (bootRun copyLoopBody s).mem_domain = s.mem_domain /\
  (bootRun copyLoopBody s).pc =
    (if s.regs 6 + 8w <+ s.regs 7 then s.pc else s.pc + 20w)
Proof
  simp (enc_lengths @ [bootRun_def,copy_loop_body,bootAfter_def,
    asm_def,inst_def,mem_op_def,arith_upd_def,binop_upd_def,
    reg_imm_def,read_reg_def,upd_pc_def,upd_reg_def,jump_to_offset_def,
    word_cmp_def,store_pc,GSYM copyWord_def,copyWord_frame,load_frame,
    APPLY_UPDATE_THM,WORD_ADD_ASSOC,
    EVAL ``i2w (8:int) : word64``, EVAL ``i2w (-16:int) : word64``]) >> rw [] >> simp [APPLY_UPDATE_THM,copyWord_frame]
QED
val _ = if null (hyp copy_loop_effect) then ignore (check_thm copy_loop_effect)
  else failwith "copy loop proof has assumptions";
