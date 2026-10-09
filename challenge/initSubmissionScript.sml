Theory initSubmission
Ancestors initMachine
Libs preamble wordsLib
Datatype:
  submission = <| code : word8 list; anchorPc : num;
    names : ffiname list; first : num; extra : init_mmio list |>
End
Definition submissionSharedDomain_def:
  submissionSharedDomain (a:word64) =
    ((inputStart <= w2n a /\ w2n a < inputEnd) \/
     (outputStart <= w2n a /\ w2n a < outputEnd))
End
Definition submissionMemoryDomain_def:
  submissionMemoryDomain (a:word64) =
    (((initialPc <= w2n a /\ w2n a < initialPc + codeSizeLimit) \/
      (ramStart <= w2n a /\ w2n a < ramEnd)) /\ ~submissionSharedDomain a)
End
Definition programDomain_def:
  programDomain s (a:word64) =
    (submissionMemoryDomain a /\
     !i. i < s.first + 2 ==> a <> n2w s.anchorPc - n2w (ffiOffset*(i+1)))
End
Definition submissionConfig_def:
  submissionConfig s = challengeMachineConfig (n2w s.anchorPc)
    (programDomain s) submissionSharedDomain s.names s.first s.extra
End
Definition initialMemory_def:
  initialMemory s input (a:word64) =
    if submissionSharedDomain a then (case guestHostMemory input a of NONE => 0w | SOME b => b) else
    if initialPc <= w2n a /\ w2n a < initialPc + LENGTH s.code then
      EL (w2n a - initialPc) s.code else 0w
End
(* Generate a completely specified zero record, including upstream fields
   absent from the reduced Lean carrier. Common fields match Lean defaults.
   No ARB term is used to initialise any machine field. *)
fun zero_value ty =
  if ty = ``:bool`` then F else
  if ty = ``:num`` then numSyntax.zero_tm else
  if wordsSyntax.is_word_type ty then wordsSyntax.mk_n2w (numSyntax.zero_tm,wordsSyntax.dest_word_type ty) else
  if can dom_rng ty then
    let val (a,b) = dom_rng ty in mk_abs (genvar a,zero_value b) end else
  if listSyntax.is_list_type ty then listSyntax.mk_nil (listSyntax.dest_list_type ty) else
  if optionSyntax.is_option ty then optionSyntax.mk_none (optionSyntax.dest_option ty) else
    let val constructor = hd (TypeBase.constructors_of ty)
        fun arguments t = case total dom_rng t of NONE => [] | SOME(a,b) => a::arguments b
    in list_mk_comb (constructor,map zero_value (arguments (type_of constructor))) end;
val zeroRiscvState_def = new_definition ("zeroRiscvState_def",
  mk_eq (mk_var ("zeroRiscvState",``:riscv_state``),zero_value ``:riscv_state``));
Definition initialState_def:
  initialState s input = zeroRiscvState with
    <| MEM8 := initialMemory s input;
       c_MCSR := (\core. (zeroRiscvState.c_MCSR core) with
         <| mstatus updated_by (\m. m with <| MPRV := 3w; VM := 0w |>);
            mcpuid updated_by (\m. m with ArchBase := 2w) |>);
       c_PC := (\core. n2w initialPc); c_gpr := (\core reg. 0w);
       c_NextFetch := (\core. NONE); exception := NoException |>
End
Definition ffiNameBoundaryValid_def:
  ffiNameBoundaryValid names first =
    (first <= LENGTH names /\ !i. i < LENGTH names ==>
      case EL i names of ExtCall _ => i < first | SharedMem _ => first <= i)
End
Definition mmioRecordValid_def:
  mmioRecordValid pc first extra index =
    case ALOOKUP (machineMmioInfo pc first extra) index of
      NONE => F | SOME (nb,a,rn,exit) => rn < 32 /\ aligned 2 exit
End
Definition admitted_def:
  admitted s <=>
    0 < LENGTH s.code /\ LENGTH s.code <= codeSizeLimit /\
    initialPc + ffiOffset*(s.first+2) < s.anchorPc /\
    s.anchorPc < initialPc + LENGTH s.code /\ aligned 2 (n2w s.anchorPc:word64) /\
    ffiNameBoundaryValid s.names s.first /\ LENGTH s.names = s.first + LENGTH s.extra /\
    (!i. i < s.first+2 ==>
      let a = n2w s.anchorPc - n2w (ffiOffset*(i+1)) : word64 in
      initialPc < w2n a /\ w2n a < initialPc + LENGTH s.code) /\
    (!i. i < LENGTH s.names /\ s.first <= i ==>
      mmioRecordValid (n2w s.anchorPc) s.first s.extra i) /\
    ALL_DISTINCT (submissionConfig s).ffi_entry_pcs /\
    (!a. MEM a (submissionConfig s).ffi_entry_pcs ==>
      initialPc < w2n a /\ w2n a < initialPc + LENGTH s.code /\
      aligned 2 a /\ a <> (submissionConfig s).halt_pc /\
      a <> (submissionConfig s).install_pc) /\
    (!rec. MEM rec s.extra ==>
      programDomain s (n2w s.anchorPc + n2w rec.entry_pc) /\
      s.anchorPc + rec.exit_pc < initialPc + LENGTH s.code) /\
    LENGTH s.code + ffiOffset*(s.first+3) < 2**64
End
Theorem initial_registers:
  (initialState s input).c_gpr core rn = 0w
Proof
  simp [initialState_def]
QED
Theorem initial_pc:
  (initialState s input).c_PC core = n2w initialPc
Proof
  simp [initialState_def]
QED

Theorem initial_state_valid:
  riscv_ok (initialState s input)
Proof
  simp [initialState_def,riscv_targetTheory.riscv_ok_def] >> EVAL_TAC
QED
Theorem admitted_code_limit:
  admitted s ==> LENGTH s.code <= codeSizeLimit
Proof
  simp [admitted_def]
QED
Theorem initial_ram_zero:
  admitted s /\ ramStart <= w2n a /\ ~submissionSharedDomain a ==>
  initialMemory s input a = 0w
Proof
  strip_tac >> drule admitted_code_limit >> strip_tac >>
  rw [initialMemory_def] >>
  fs [initParamsTheory.initialPc_def,initParamsTheory.codeSizeLimit_def,
      initParamsTheory.ramStart_def]
QED
