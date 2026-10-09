(* Challenge target restriction, independent of how submitted bytes were made.
   Constructor whitelist transcribed from the pinned Flapjack L3 carrier.
   Decoder/step agreement with Lean remains a separate proof obligation. *)
Theory initTarget
Ancestors riscv cv_std
Libs cv_transLib bitstringLib

Definition supported_instruction_def:
  supported_instruction (riscv$ArithI (riscv$ADDI args)) = T /\
  supported_instruction (riscv$ArithI (riscv$ADDIW args)) = T /\
  supported_instruction (riscv$ArithI (riscv$ANDI args)) = T /\
  supported_instruction (riscv$ArithI (riscv$AUIPC args)) = T /\
  supported_instruction (riscv$ArithI (riscv$LUI args)) = T /\
  supported_instruction (riscv$ArithI (riscv$ORI args)) = T /\
  supported_instruction (riscv$ArithI (riscv$SLTI args)) = T /\
  supported_instruction (riscv$ArithI (riscv$SLTIU args)) = T /\
  supported_instruction (riscv$ArithI (riscv$XORI args)) = T /\
  supported_instruction (riscv$ArithR (riscv$ADD args)) = T /\
  supported_instruction (riscv$ArithR (riscv$AND args)) = T /\
  supported_instruction (riscv$ArithR (riscv$OR args)) = T /\
  supported_instruction (riscv$ArithR (riscv$SLT args)) = T /\
  supported_instruction (riscv$ArithR (riscv$SLTU args)) = T /\
  supported_instruction (riscv$ArithR (riscv$SUB args)) = T /\
  supported_instruction (riscv$ArithR (riscv$XOR args)) = T /\
  supported_instruction (riscv$Branch (riscv$BEQ args)) = T /\
  supported_instruction (riscv$Branch (riscv$BGE args)) = T /\
  supported_instruction (riscv$Branch (riscv$BGEU args)) = T /\
  supported_instruction (riscv$Branch (riscv$BLT args)) = T /\
  supported_instruction (riscv$Branch (riscv$BLTU args)) = T /\
  supported_instruction (riscv$Branch (riscv$BNE args)) = T /\
  supported_instruction (riscv$Branch (riscv$JAL args)) = T /\
  supported_instruction (riscv$Branch (riscv$JALR args)) = T /\
  supported_instruction (riscv$Load (riscv$LB args)) = T /\
  supported_instruction (riscv$Load (riscv$LBU args)) = T /\
  supported_instruction (riscv$Load (riscv$LD args)) = T /\
  supported_instruction (riscv$Load (riscv$LH args)) = T /\
  supported_instruction (riscv$Load (riscv$LHU args)) = T /\
  supported_instruction (riscv$Load (riscv$LW args)) = T /\
  supported_instruction (riscv$Load (riscv$LWU args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$DIV args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$DIVU args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$MUL args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$MULH args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$MULHSU args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$MULHU args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$REM args)) = T /\
  supported_instruction (riscv$MulDiv (riscv$REMU args)) = T /\
  supported_instruction (riscv$Shift (riscv$SLL args)) = T /\
  supported_instruction (riscv$Shift (riscv$SLLI args)) = T /\
  supported_instruction (riscv$Shift (riscv$SRA args)) = T /\
  supported_instruction (riscv$Shift (riscv$SRAI args)) = T /\
  supported_instruction (riscv$Shift (riscv$SRL args)) = T /\
  supported_instruction (riscv$Shift (riscv$SRLI args)) = T /\
  supported_instruction (riscv$Store (riscv$SB args)) = T /\
  supported_instruction (riscv$Store (riscv$SD args)) = T /\
  supported_instruction (riscv$Store (riscv$SH args)) = T /\
  supported_instruction (riscv$Store (riscv$SW args)) = T /\
  supported_instruction (riscv$System (riscv$EBREAK)) = T /\
  supported_instruction (riscv$System (riscv$ECALL)) = T /\
  supported_instruction (riscv$FENCE args) = T /\
  supported_instruction _ = F
End

Definition restricted_decode_def:
  restricted_decode w =
    let i = riscv$Decode w in
    if supported_instruction i then i else riscv$UnknownInstruction
End

Definition restricted_decode_rvc_def:
  restricted_decode_rvc (h:word16) = riscv$UnknownInstruction
End

(* Reuse the upstream step body, replacing both decoders. This preserves
   dynamic instruction fetching: data and unreachable ROM are not rejected
   by a blanket scan. Unsupported fetched words take the unknown-instruction
   path of the L3 machine. *)
val restricted_next_body =
  rhs (concl (SPEC_ALL riscvTheory.Next_def))
  |> subst [``riscv$Decode`` |-> ``restricted_decode``,
            ``riscv$DecodeRVC`` |-> ``restricted_decode_rvc``];
val restricted_next_def = new_definition ("restricted_next_def",
  mk_eq (mk_comb (mk_var ("restricted_next", type_of ``riscv$Next``),
                   rand (lhs (concl (SPEC_ALL riscvTheory.Next_def)))),
         restricted_next_body));

Theorem rejected_instruction:
  ~supported_instruction (riscv$Decode w) ==>
  restricted_decode w = riscv$UnknownInstruction
Proof
  simp [restricted_decode_def]
QED

Theorem supported_decode:
  supported_instruction (riscv$Decode w) ==>
  restricted_decode w = riscv$Decode w
Proof
  simp [restricted_decode_def]
QED

Theorem compressed_rejected:
  !h. restricted_decode_rvc h = riscv$UnknownInstruction
Proof
  simp [restricted_decode_rvc_def]
QED

Theorem subset_regression:
  supported_instruction (riscv$ArithI (riscv$ADDIW (1w,2w,0w))) /\
  ~supported_instruction (riscv$ArithR (riscv$ADDW (1w,2w,3w))) /\
  ~supported_instruction (riscv$MulDiv (riscv$MULW (1w,2w,3w))) /\
  ~supported_instruction (riscv$Shift (riscv$SLLW (1w,2w,3w))) /\
  ~supported_instruction (riscv$System riscv$ERET)
Proof
  EVAL_TAC
QED

(* Raw participant instruction words, including encodings accepted by upstream
   RISC-V but excluded by this challenge. These are execution-time checks. *)
val decode_conv = computeLib.compset_conv wordsLib.words_compset
  [computeLib.Defs (restricted_decode_def :: supported_instruction_def ::
                    map snd (DB.definitions "riscv")),
   computeLib.Extenders [bitstringLib.add_bitstring_compset]];

Theorem decode_regression:
  restricted_decode 0x00000013w = riscv$ArithI (riscv$ADDI (0w,0w,0w)) /\
  restricted_decode 0x02000033w = riscv$MulDiv (riscv$MUL (0w,0w,0w)) /\
  restricted_decode 0x00000073w = riscv$System riscv$ECALL /\
  restricted_decode 0x0000003bw = riscv$UnknownInstruction /\
  restricted_decode 0x00000053w = riscv$UnknownInstruction /\
  restricted_decode 0x0000100fw = riscv$UnknownInstruction /\
  restricted_decode 0x00000000w = riscv$UnknownInstruction
Proof
  CONV_TAC decode_conv >>
  CONV_TAC (DEPTH_CONV bitstringLib.v2w_n2w_CONV) >> EVAL_TAC
QED
