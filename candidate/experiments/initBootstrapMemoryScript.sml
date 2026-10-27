(* Memory and register facts for the bootstrap's actual LD/SD copy pair.
   Frame proofs follow CakeML asmProps (see ../CAKEML-LICENSE). *)
Theory initBootstrapMemory
Ancestors asmSem
Libs preamble wordsLib

Theorem read_word_frame:
  !n a (s:64 asm_state).
    (SND (read_mem_word a n s)).regs = s.regs /\
    (SND (read_mem_word a n s)).mem = s.mem /\
    (SND (read_mem_word a n s)).pc = s.pc /\
    (SND (read_mem_word a n s)).be = s.be /\
    (SND (read_mem_word a n s)).mem_domain = s.mem_domain
Proof
  Induct >> fs [read_mem_word_def,LET_DEF] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> fs [assert_def]
QED
Theorem write_word_frame:
  !n a w (s:64 asm_state).
    (write_mem_word a n w s).regs = s.regs /\
    (write_mem_word a n w s).pc = s.pc /\
    (write_mem_word a n w s).be = s.be /\
    (write_mem_word a n w s).mem_domain = s.mem_domain
Proof
  Induct >> fs [write_mem_word_def,LET_DEF,assert_def,upd_mem_def]
QED
Definition copyWord_def:
  copyWord (s:64 asm_state) =
    mem_store 8 28 (Addr 6 0) (mem_load 8 28 (Addr 5 0) s)
End
Theorem load_registers:
  !n rn a (s:64 asm_state).
    (mem_load n rn a s).regs =
      (rn =+ FST (read_mem_word
        (if s.be then addr a s + n2w (n-1) else addr a s) n s)) s.regs
Proof
  rw [mem_load_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp [assert_def,upd_reg_def,read_word_frame]
QED
Theorem load_frame:
  !n rn a (s:64 asm_state).
    (mem_load n rn a s).pc = s.pc /\
    (mem_load n rn a s).be = s.be /\
    (mem_load n rn a s).mem = s.mem /\
    (mem_load n rn a s).mem_domain = s.mem_domain
Proof
  rw [mem_load_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp [assert_def,upd_reg_def,read_word_frame]
QED
Theorem copyWord_frame:
  (copyWord s).pc = s.pc /\ (copyWord s).be = s.be /\
  (copyWord s).mem_domain = s.mem_domain /\
  (!rn. rn <> 28 ==> (copyWord s).regs rn = s.regs rn)
Proof
  simp [copyWord_def,mem_store_def,write_word_frame,assert_def,load_registers] >>
  simp [mem_load_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp [assert_def,upd_reg_def,read_word_frame,APPLY_UPDATE_THM]
QED
Theorem read_word_value:
  !n a (s:64 asm_state). ~s.be ==>
    FST (read_mem_word a n s) =
      if n = 0 then 0w else
        FST (read_mem_word (a+1w) (n-1) s) << 8 || w2w (s.mem a)
Proof
  Cases >> simp [read_mem_word_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp [read_mem_def,read_word_frame]
QED
Theorem write_word_byte:
  !n a w (s:64 asm_state) x. ~s.be ==>
    (write_mem_word a n w s).mem x =
      if n = 0 then s.mem x else if x = a then w2w w else
        (write_mem_word (a+1w) (n-1) (w >>> 8) s).mem x
Proof
  Cases >> simp [write_mem_word_def,assert_def,upd_mem_def,APPLY_UPDATE_THM] >>
  metis_tac []
QED
Theorem read_word_selected:
  ~(s:64 asm_state).be ==> !j. j < 8 ==>
    (w2w ((FST (read_mem_word a 8 s) : word64) >>> (8*j)) : word8) = s.mem (a+n2w j)
Proof
  strip_tac >>
  CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV)) >>
  fs [read_word_value,WORD_ADD_ASSOC] >> WORD_DECIDE_TAC
QED
Theorem write_word_selected:
  ~(s:64 asm_state).be ==> !j. j < 8 ==>
    (write_mem_word a 8 (w:word64) s).mem (a+n2w j) = (w2w (w >>> (8*j)) : word8)
Proof
  strip_tac >>
  CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV)) >>
  fs [write_word_byte,WORD_ADD_ASSOC] >> WORD_DECIDE_TAC
QED
Theorem copyWord_bytes:
  ~s.be ==> !j. j < 8 ==>
    (copyWord s).mem (s.regs 6 + n2w j) = s.mem (s.regs 5 + n2w j)
Proof
  rw [copyWord_def,mem_store_def,assert_def] >>
  fs [load_frame,addr_def,read_reg_def,load_registers,APPLY_UPDATE_THM,
      write_word_selected,read_word_selected,integer_wordTheory.i2w_0,
      ONCE_REWRITE_RULE [WORD_ADD_COMM] write_word_selected,
      ONCE_REWRITE_RULE [WORD_ADD_COMM] read_word_selected]
QED
Theorem write_word_outside:
  ~(s:64 asm_state).be /\ (!j. j < 8 ==> x <> a+n2w j) ==>
    (write_mem_word a 8 (w:word64) s).mem x = s.mem x
Proof
  strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV))) >>
  fs [write_word_byte,WORD_ADD_ASSOC]
QED
Theorem copyWord_outside:
  ~s.be /\ (!j. j < 8 ==> x <> s.regs 6 + n2w j) ==>
    (copyWord s).mem x = s.mem x
Proof
  rw [copyWord_def,mem_store_def,assert_def] >>
  fs [load_frame,addr_def,read_reg_def,load_registers,APPLY_UPDATE_THM,
      write_word_outside,integer_wordTheory.i2w_0]
QED
Theorem read_word_failed:
  !n a (s:64 asm_state). ~s.be ==>
    (SND (read_mem_word a n s : word64 # 64 asm_state)).failed =
      if n = 0 then s.failed else
        ~(a IN s.mem_domain) \/
        (SND (read_mem_word (a+1w) (n-1) s : word64 # 64 asm_state)).failed
Proof
  Cases >> simp [read_mem_word_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp [assert_def,read_word_frame]
QED
Theorem write_word_failed:
  !n a (w:word64) (s:64 asm_state). ~s.be ==>
    (write_mem_word a n w s).failed =
      if n = 0 then s.failed else
        ~(a IN s.mem_domain) \/ (write_mem_word (a+1w) (n-1) (w >>> 8) s).failed
Proof
  Cases >> simp [write_mem_word_def,assert_def,upd_mem_def,write_word_frame]
QED
Theorem load_failed:
  !n rn a (s:64 asm_state).
    (mem_load n rn a s).failed =
      (~aligned (LOG2 n) (addr a s) \/
      (SND (read_mem_word
        (if s.be then addr a s + n2w (n-1) else addr a s) n s
        : word64 # 64 asm_state)).failed)
Proof
  rw [mem_load_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp [assert_def,upd_reg_def]
QED
Theorem copyWord_success:
  ~s.be /\ ~s.failed /\ aligned 3 (s.regs 5) /\ aligned 3 (s.regs 6) /\
  (!j. j < 8 ==> s.regs 5 + n2w j IN s.mem_domain) /\
  (!j. j < 8 ==> s.regs 6 + n2w j IN s.mem_domain) ==>
  ~(copyWord s).failed
Proof
  strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV))) >>
  fs [copyWord_def,mem_store_def,assert_def,write_word_failed,
      load_frame,load_failed,read_word_failed,addr_def,read_reg_def,
      load_registers,APPLY_UPDATE_THM,integer_wordTheory.i2w_0,WORD_ADD_ASSOC]
QED
Theorem read_word_pc:
  !n a (s:64 asm_state) pc.
    (read_mem_word a n (s with pc := pc) : word64 # 64 asm_state) =
    (FST (read_mem_word a n s),
     SND (read_mem_word a n s : word64 # 64 asm_state) with pc := pc)
Proof
  Induct >> fs [read_mem_word_def,LET_DEF] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> fs [assert_def,read_mem_def]
QED
Theorem write_word_pc:
  !n a (w:word64) (s:64 asm_state) pc.
    write_mem_word a n w (s with pc := pc) =
    (write_mem_word a n w s) with pc := pc
Proof
  Induct >> fs [write_mem_word_def,LET_DEF,assert_def,upd_mem_def]
QED
Theorem load_pc:
  mem_load n rn a ((s:64 asm_state) with pc := pc) =
  (mem_load n rn a s) with pc := pc
Proof
  Cases_on `a` >> simp [mem_load_def,addr_def,read_reg_def,read_word_pc] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> simp [assert_def,upd_reg_def]
QED
Theorem store_pc:
  mem_store n rn a ((s:64 asm_state) with pc := pc) =
  (mem_store n rn a s) with pc := pc
Proof
  Cases_on `a` >> simp [mem_store_def,addr_def,read_reg_def,write_word_pc,assert_def]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "bootstrap memory assumptions")
  [read_word_frame,write_word_frame,load_registers,copyWord_frame,load_frame,read_word_value,write_word_byte,read_word_selected,
   write_word_selected,copyWord_bytes,write_word_outside,copyWord_outside,
   read_word_failed,write_word_failed,load_failed,copyWord_success,
   read_word_pc,write_word_pc,load_pc,store_pc];
