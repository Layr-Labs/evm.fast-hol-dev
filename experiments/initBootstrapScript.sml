(* The baseline bootstrap starts with zero RAM. Layout and encoder results
   are checked here; the execution/installation proof is a separate obligation. *)
Theory initBootstrap
Ancestors riscvTargetCv initParams
Libs preamble cv_transLib wordsLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
(* Place the exact native image so its end matches the fixed source header. *)
Definition baselineNativePc_def:
  baselineNativePc : num = 0x80000f60
End
Definition bootDataRom_def:
  bootDataRom : num = 0x800df000
End
Definition bootDataRam_def:
  bootDataRam : num = 0xa0020000
End
Definition bootDataEnd_def:
  bootDataEnd : num = 0xa0029048
End
Definition bootLoc_def:
  bootLoc rn (pc:num) (address:num) = asm$Loc rn (&address - &pc)
End
Definition bootConst_def:
  bootConst rn (value:num) = asm$Inst (asm$Const rn (&value))
End
Definition bootShift_def:
  bootShift rn (amount:num) = asm$Inst (asm$Arith (asm$Shift Lsl rn rn (asm$Imm (&amount))))
End
Definition bootStore_def:
  bootStore rn base (offset:num) = asm$Inst (asm$Mem asm$Store rn (asm$Addr base (&offset)))
End
Definition bootAdd_def:
  bootAdd rn = asm$Inst (asm$Arith (asm$Binop asm$Add rn rn (asm$Imm 8)))
End
Definition bootstrapBlocks_def:
  bootstrapBlocks : (num # asm) list = [

  (0x80000000, bootLoc 5 0x80000000 bootDataRom);
  (0x80000008, bootLoc 6 0x80000008 bootDataRam);
  (0x80000010, bootLoc 7 0x80000010 bootDataEnd);
  (0x80000018, asm$Inst (asm$Mem asm$Load 28 (asm$Addr 5 0)));
  (0x8000001c, bootStore 28 6 0);
  (0x80000020, bootAdd 5);
  (0x80000024, bootAdd 6);
  (0x80000028, asm$JumpCmp asm$Lower 6 (asm$Reg 7) (-16));
  (0x8000002c, bootLoc 5 0x8000002c bootDataRam);
  (0x80000034, bootConst 6 161);
  (0x80000038, bootShift 6 24);
  (0x8000003c, bootStore 6 5 0);
  (0x80000040, bootLoc 5 0x80000040 (bootDataRam+8));
  (0x80000048, bootConst 6 2015);
  (0x8000004c, bootShift 6 24);
  (0x80000050, bootStore 6 5 0);
  (0x80000054, bootLoc 5 0x80000054 (bootDataRam+16));
  (0x8000005c, bootConst 6 63);
  (0x80000060, bootShift 6 29);
  (0x80000064, bootStore 6 5 0);
  (0x80000068, bootConst 5 161);
  (0x8000006c, bootShift 5 24);
  (0x80000070, bootLoc 6 0x80000070 (bootDataRam+24));
  (0x80000078, bootStore 6 5 0);
  (0x8000007c, bootLoc 6 0x8000007c bootDataEnd);
  (0x80000084, bootStore 6 5 8);
  (0x80000088, bootLoc 6 0x80000088 bootDataEnd);
  (0x80000090, bootStore 6 5 16);
  (0x80000094, bootLoc 6 0x80000094 0x800ddd08);
  (0x8000009c, bootStore 6 5 24);
  (0x800000a0, bootLoc 6 0x800000a0 0x800de000);
  (0x800000a8, bootStore 6 5 32);
  (0x800000ac, bootConst 11 161);
  (0x800000b0, bootShift 11 24);
  (0x800000b4, bootConst 12 2015);
  (0x800000b8, bootShift 12 24);
  (0x800000bc, bootConst 13 63);
  (0x800000c0, bootShift 13 29);
  (0x800000c4, bootLoc 10 0x800000c4 baselineNativePc);
  (0x800000cc, asm$Jump (&baselineNativePc - 0x800000cc))
  ]
End
Definition bootstrapBytes_def:
  bootstrapBytes = FLAT (MAP (\block. riscv_enc (SND block)) bootstrapBlocks)
End
val _ = cv_auto_trans bootstrapBytes_def;
fun save_closed name th = if null (hyp th) then save_thm (name,check_thm th)
  else failwith "bootstrap theorem has assumptions";
val _ = save_closed "bootstrap_size" (EQT_ELIM (cv_eval ``LENGTH bootstrapBytes = 208``));
Theorem bootstrap_instructions_admitted:
  EVERY (\block. asm_ok (SND block) riscv_config) bootstrapBlocks
Proof
  EVAL_TAC
QED
Theorem bootstrap_layout:
  baselineNativePc - initialPc = 3936 /\
  baselineNativePc + 904616 = 0x800ddd08 /\
  0x800de000 <= bootDataRom /\
  bootDataEnd - bootDataRam = 8 * (3 + 4614) /\
  initialPc + 208 < baselineNativePc - 16 * (20 + 2)
Proof
  EVAL_TAC
QED
val th = cv_eval_raw ``bootstrapBytes``;
val _ = check_thm th;
val output = BinIO.openOut "bootstrap.bin";
fun emit tm = if cvSyntax.is_cv_pair tm then
  let val (n,rest) = cvSyntax.dest_cv_pair tm
      val b = numSyntax.int_of_term (cvSyntax.dest_cv_num n)
  in if 0 <= b andalso b < 256 then
       (BinIO.output1(output,Word8.fromInt b);emit rest)
     else failwith "bootstrap byte out of range" end
  else if aconv tm (cvSyntax.mk_cv_num numSyntax.zero_tm) then ()
  else failwith "bootstrap byte list malformed";
val _ = emit (rand (rconc th));
val _ = BinIO.closeOut output;
