(* CakeML-derived portions are covered by ../CAKEML-LICENSE. *)
(* Fixed machine construction and cache-hook evaluator. The upstream install
   hook is not the init-e cache hook; challengeEvaluate defines that case
   explicitly instead of silently substituting installation semantics. *)
Theory initMachine
Ancestors initSource initTarget riscv_target targetSem
Libs preamble wordsLib
(* The challenge's layout uses natural offsets, as in init-e's reduced
   carrier; do not silently widen participant metadata to signed offsets. *)
Datatype:
  init_mmio = <| entry_pc : num; nbytes : word8; addr_reg : num;
                 addr_off : num; reg : num; exit_pc : num |>
End
Definition ffiOffset_def:
  ffiOffset : num = 16
End
Definition machineSetPc_def:
  machineSetPc (s:riscv_state) pc = s with c_PC := (s.procID =+ pc) s.c_PC
End
Definition machineSetReg_def:
  machineSetReg (s:riscv_state) reg value = s with
    c_gpr := (s.procID =+ ((n2w reg =+ value) (s.c_gpr s.procID))) s.c_gpr
End
Definition machineExtReturn_def:
  machineExtReturn (s:riscv_state) bytes =
    machineSetPc (s with MEM8 := asm_write_bytearray (s.c_gpr s.procID 12w) bytes s.MEM8)
      (s.c_gpr s.procID 1w)
End
Definition machineMmioReturn_def:
  machineMmioReturn s name (nb,a,reg,pc) bytes =
    machineSetPc (if name = SharedMem MappedRead then
      machineSetReg s reg (word_of_bytes F 0w bytes) else s) pc
End
Definition machineFfiInterference_def:
  machineFfiInterference names info n (index,bytes,s) =
    case ALOOKUP info index of
      NONE => machineExtReturn s bytes
    | SOME record => machineMmioReturn s (EL index names) record bytes
End
Definition machineMmioInfo_def:
  machineMmioInfo (pc:word64) first (extra:init_mmio list) =
    ZIP (GENLIST (\i. i+first) (LENGTH extra),
      MAP (\rec. (rec.nbytes, Addr rec.addr_reg (&rec.addr_off),
                   rec.reg, n2w rec.exit_pc + pc)) extra)
End
Definition restrictedDecodeAny_def:
  restrictedDecodeAny (riscv$Word w) = restricted_decode w /\
  restrictedDecodeAny (riscv$Half h) = restricted_decode_rvc h
End
val step_body = rhs (concl (SPEC_ALL riscv_stepTheory.NextRISCV_def))
  |> subst [``riscv_step$DecodeAny`` |-> ``restrictedDecodeAny``];
val restrictedNextRISCV_def = new_definition ("restrictedNextRISCV_def",
  mk_eq (mk_comb (mk_var ("restrictedNextRISCV",type_of ``riscv_step$NextRISCV``),
                 rand (lhs (concl (SPEC_ALL riscv_stepTheory.NextRISCV_def)))),step_body));
Definition restrictedTarget_def:
  restrictedTarget = riscv_target with next := (\s. THE (restrictedNextRISCV s))
End
Definition challengeMachineConfig_def:
  challengeMachineConfig (pc:word64) program shared names first extra =
    <| prog_addresses := program; shared_addresses := shared;
       ffi_entry_pcs := GENLIST (\i. pc - n2w ((3+i)*ffiOffset)) first ++
         MAP (\rec. pc + n2w rec.entry_pc) extra;
       ffi_names := names; ptr_reg := 10; len_reg := 11; ptr2_reg := 12; len2_reg := 13;
       ffi_interfer := machineFfiInterference names (machineMmioInfo pc first extra);
       callee_saved_regs := [24;25;26]; next_interfer := (\n s. s);
       halt_pc := pc - n2w ffiOffset; install_pc := pc - n2w (2*ffiOffset);
       install_interfer := (\n (bytes,s). s);
       target := restrictedTarget; mmio_info := machineMmioInfo pc first extra |>
End
Definition challengeEvaluate_def:
  challengeEvaluate (mc:(64,riscv_state,'c) machine_config) (ffi:'ffi ffi_state) k (ms:riscv_state) =
    if k = 0 then (TimeOut,ms,ffi)
    else
      if (mc.target.get_pc ms) IN (mc.prog_addresses DIFF (set mc.ffi_entry_pcs)) then
        if encoded_bytes_in_mem
            mc.target.config (mc.target.get_pc ms)
            (mc.target.get_byte ms) mc.prog_addresses then
          let ms1 = mc.target.next ms in
          let (ms2,new_oracle) = apply_oracle mc.next_interfer ms1 in
          let mc = mc with next_interfer := new_oracle in
            if EVERY mc.target.state_ok [ms;ms1;ms2] ∧
               (∀x. x ∉ mc.prog_addresses ⇒
                   mc.target.get_byte ms1 x =
                   mc.target.get_byte ms x)
            then
              challengeEvaluate mc ffi (k - 1) ms2
            else
              (Error,ms,ffi)
        else (Error,ms,ffi)
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then Halt Success else Halt Resource_limit_hit,ms,ffi)
      else if mc.target.get_pc ms = mc.install_pc then
         challengeEvaluate mc ffi (k-1)
           (machineSetPc ms (mc.target.get_reg ms 1))
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => (Error,ms,ffi)
        | SOME ffi_index =>
            (case EL ffi_index mc.ffi_names of
             | SharedMem op =>
                 (case ALOOKUP mc.mmio_info ffi_index of
                  | NONE => (Error, ms, ffi)
                  | SOME (nb,a,rn,pc') =>
                      (case op of
                         | MappedRead =>
                             (case a of
                              | Addr r off =>
                                  let ad = mc.target.get_reg ms r + i2w off in
                                    (if (if nb = 0w
                                         then (w2n ad MOD (dimindex (:64) DIV 8)) = 0 else T) ∧
                                        (ad IN mc.shared_addresses) ∧
                                        is_valid_mapped_read (mc.target.get_pc ms) nb a rn pc'
                                                             mc.target ms mc.prog_addresses
                                     then
                                       (case call_FFI ffi (EL ffi_index mc.ffi_names) [nb]
                                                      (word_to_bytes ad F) of
                                        | FFI_final outcome =>
                                            (Halt (FFI_outcome outcome),ms,ffi)
                                        | FFI_return new_ffi new_bytes =>
                                            let (ms1,new_oracle)
                                                = apply_oracle mc.ffi_interfer
                                                               (ffi_index,new_bytes,ms) in
                                              let mc = mc with ffi_interfer := new_oracle in
                                                challengeEvaluate mc new_ffi (k - 1:num) ms1)
                                     else (Error,ms,ffi)))
                         | MappedWrite =>
                             (case a of
                              | Addr r off =>
                                  let ad = (mc.target.get_reg ms r) + i2w off in
                                    (if (if nb = 0w
                                         then (w2n ad MOD (dimindex (:64) DIV 8)) = 0 else T) ∧
                                        (ad IN mc.shared_addresses) ∧
                                        is_valid_mapped_write (mc.target.get_pc ms) nb a rn pc'
                                                              mc.target ms mc.prog_addresses
                                     then
                                       (case call_FFI ffi (EL ffi_index mc.ffi_names) [nb]
                                                      ((let w = mc.target.get_reg ms rn in
                                                          if nb = 0w then word_to_bytes w F
                                                          else word_to_bytes_aux (w2n nb) w F)
                                                       ++ (word_to_bytes ad F)) of
                                        | FFI_final outcome =>
                                            (Halt (FFI_outcome outcome),ms,ffi)
                                        | FFI_return new_ffi new_bytes =>
                                            let (ms1,new_oracle)
                                                = apply_oracle mc.ffi_interfer
                                                               (ffi_index,new_bytes,ms) in
                                              let mc = mc with ffi_interfer := new_oracle in
                                                challengeEvaluate mc new_ffi (k - 1:num) ms1)
                                     else (Error,ms,ffi)))))
             | ExtCall _ =>
                 (case ALOOKUP mc.mmio_info ffi_index of
                  | SOME _ => (Error, ms, ffi)
                  | NONE =>
                      (case read_ffi_bytearrays mc ms of
                       | (SOME bytes, SOME bytes2) =>
                           (case call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 of
                            | FFI_final outcome => (Halt (FFI_outcome outcome),ms,ffi)
                            | FFI_return new_ffi new_bytes =>
                                let (ms1,new_oracle)
                                    = apply_oracle mc.ffi_interfer
                                                   (ffi_index,new_bytes,ms) in
                                  let mc = mc with ffi_interfer := new_oracle in
                                    challengeEvaluate mc new_ffi (k - 1:num) ms1)
                       | _ => (Error,ms,ffi))))
End

Theorem challenge_timeout:
  challengeEvaluate mc ffi 0 ms = (TimeOut,ms,ffi)
Proof
  simp [Once challengeEvaluate_def]
QED
Theorem challenge_cache_return:
  ~(mc.target.get_pc ms IN (mc.prog_addresses DIFF set mc.ffi_entry_pcs)) /\
  mc.target.get_pc ms <> mc.halt_pc /\ mc.target.get_pc ms = mc.install_pc ==>
  challengeEvaluate mc ffi (SUC k) ms =
    challengeEvaluate mc ffi k (machineSetPc ms (mc.target.get_reg ms 1))
Proof
  strip_tac >> CONV_TAC (LAND_CONV (REWR_CONV challengeEvaluate_def)) >> fs []
QED
