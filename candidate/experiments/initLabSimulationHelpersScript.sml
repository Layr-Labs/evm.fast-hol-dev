(* Local helper lemmas from pinned CakeML lab_to_targetProof, exposed for
   the fixed challenge evaluator simulation. See ../CAKEML-LICENSE. *)
Theory initLabSimulationHelpers
Ancestors lab_to_targetProof
Libs preamble BasicProvers
open ffiTheory wordSemTheory labSemTheory labPropsTheory lab_to_targetTheory
  lab_filterProofTheory asmTheory asmSemTheory asmPropsTheory targetSemTheory
  targetPropsTheory backendPropsTheory lab_to_targetProofTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val s1 = ``s1:('a,lab_to_target$config,'ffi) labSem$state``;
Theorem enc_with_nop_thm:
  enc_with_nop enc (b:asm) bytes =
      ?n. bytes = enc b ++ FLAT (REPLICATE n (enc (asm$Inst Skip)))
Proof
  fs [enc_with_nop_def,LENGTH_NIL]
  \\ IF_CASES_TAC \\ fs [FLAT_REPLICATE_NIL]
  \\ EQ_TAC \\ rw [] THEN1 metis_tac []
  \\ fs [LENGTH_APPEND,LENGTH_FLAT,map_replicate,SUM_REPLICATE]
  \\ full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL,MULT_DIV]
QED

Theorem lab_lookup_IMP:
  (lab_lookup l1 l2 labs = SOME x) ==>
    (find_pos (Lab l1 l2) labs = x)
Proof
  full_simp_tac(srw_ss())[lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC
QED

Theorem prog_to_bytes_lemma:
  !code2 code1 pc i pos.
      code_similar code1 code2 /\
      all_enc_ok (mc_conf:('a,'state,'b) machine_config).target.config
        labs ffi_names pos code2 /\
      (asm_fetch_aux pc code1 = SOME i) ==>
      ?bs j bs2.
        (prog_to_bytes code2 = bs ++ line_bytes j ++ bs2) /\
        (LENGTH bs + pos = pos_val pc pos code2) /\
        (LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc+1) pos code2) /\
        line_similar i j /\
        line_ok mc_conf.target.config labs ffi_names (pos_val pc pos code2) j
Proof
  HO_MATCH_MP_TAC asm_code_length_ind \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def,asm_fetch_aux_def])
  THEN1
   (Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def]
    \\ Cases_on `h` \\ full_simp_tac(srw_ss())[code_similar_def]
    \\ Cases_on `l` \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,pos_val_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,all_enc_ok_def] \\ metis_tac [])
  \\ Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[code_similar_def]
  \\ Cases_on`l` \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,pos_val_def]
  \\ rpt var_eq_tac
  \\ Q.MATCH_ASSUM_RENAME_TAC `line_similar x1 x2`
  \\ Q.MATCH_ASSUM_RENAME_TAC `LIST_REL line_similar ys1 ys2`
  \\ `is_Label x2 = is_Label x1` by
    (Cases_on `x1` \\ Cases_on `x2` \\ full_simp_tac(srw_ss())[line_similar_def,is_Label_def])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `is_Label x1` \\ full_simp_tac(srw_ss())[]
  THEN1
   (full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
    \\ full_simp_tac(srw_ss())[all_enc_ok_def,code_similar_def] \\ rpt strip_tac
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
    \\ Cases_on `x2` \\ full_simp_tac(srw_ss())[line_ok_def,is_Label_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[line_length_def,line_bytes_def]
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  \\ Cases_on `pc = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1
   (full_simp_tac(srw_ss())[listTheory.LENGTH_NIL] \\ qexists_tac `x2`
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF,all_enc_ok_def] \\ full_simp_tac(srw_ss())[pos_val_0]
    \\ imp_res_tac pos_val_0
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `x2`
    \\ full_simp_tac(srw_ss())[line_ok_def,is_Label_def,line_bytes_def,line_length_def] \\ srw_tac[][])
  \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc-1`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
  \\ full_simp_tac(srw_ss())[all_enc_ok_def,code_similar_def]
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
  \\ Q.LIST_EXISTS_TAC [`line_bytes x2 ++ bs`,
        `j`,`bs2`] \\ full_simp_tac(srw_ss())[] \\ `pc - 1 + 1 = pc` by decide_tac
  \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
QED

val prog_to_bytes_lemma = prog_to_bytes_lemma
  |> Q.SPECL [`code2`,`code1`,`pc`,`i`,`0`]
  |> SIMP_RULE std_ss [];

Theorem bytes_in_mem_APPEND:
  !xs ys a m md md1.
      bytes_in_mem a (xs ++ ys) m md md1 <=>
      bytes_in_mem a xs m md md1 /\
      bytes_in_mem (a + n2w (LENGTH xs)) ys m md md1
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def,ADD1,GSYM word_add_n2w,CONJ_ASSOC]
QED

Theorem IMP_bytes_in_memory:
  code_similar code1 code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    (asm_fetch_aux pc code1 = SOME i) /\
    bytes_in_mem p (prog_to_bytes code2) m (dm:'a word set) dm1 ==>
    ?j.
      bytes_in_mem (p + n2w (pos_val pc 0 code2)) (line_bytes j) m dm dm1 /\
      line_ok (mc_conf:('a,'state,'b) machine_config).target.config
        labs ffi_names (pos_val pc 0 code2) j /\
      (pos_val (pc+1) 0 code2 = pos_val pc 0 code2 + LENGTH (line_bytes j)) /\
      line_similar i j
Proof
  rpt strip_tac
  \\ mp_tac prog_to_bytes_lemma \\ fs[] \\ rpt strip_tac
  \\ fs[bytes_in_mem_APPEND]
  \\ Q.EXISTS_TAC `j` \\ fs[] \\ decide_tac
QED

Theorem IMP_bytes_in_memory_JumpReg:
  code_similar s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Asmi (JumpReg r1)) l n)) ==>
    bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      (mc_conf.target.config.encode (JumpReg r1)) t1.mem t1.mem_domain /\
    asm_ok (JumpReg r1) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,enc_with_nop_thm] \\ srw_tac[][] \\ fs[]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

val case_eq_thms0 = map TypeBase.case_eq_of [``:lab``, ``:'a option``]
val bool_case_eq_thms = map (fn th =>
  let val v = th |> concl |> lhs |> rhs
  in th |> GEN v |> Q.ISPEC`T` |> SIMP_RULE bool_ss [] end) case_eq_thms0

Theorem IMP_bytes_in_memory_Jump:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = &(find_pos jtarget labs) -
            &(pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def]
  \\ rveq
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF,get_label_def]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Theorem IMP_bytes_in_memory_JumpCmp:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = &(find_pos jtarget labs) -
            &(pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.config.encode (JumpCmp cmp rr ri tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def]
  \\ rveq
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF,get_label_def]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Theorem IMP_bytes_in_memory_JumpCmp_1:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt bytes.
      (tt = &(find_pos jtarget labs) -
            &(pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.config.encode (JumpCmp cmp rr ri tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def]
  \\ rveq
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF,get_label_def]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ Q.EXISTS_TAC `l'` \\ fs[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[line_bytes_def]
  \\ rveq \\ fs[lab_inst_def]
  \\ metis_tac[]
QED

Theorem IMP_bytes_in_memory_Call:
  code_similar ^s1.code code2 /\
    all_enc_ok
      (mc_conf: ('a,'state,'b) machine_config).target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem
      (t1:'a asm_state).mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Call ww) l bytes n)) ==>
    F
Proof
  rpt strip_tac
  \\ full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ imp_res_tac IMP_bytes_in_memory
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def] \\ rev_full_simp_tac(srw_ss())[]
QED

Theorem IMP_bytes_in_memory_LocValue:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) l bytes n)) ==>
    ?tt bytes.
      (tt = &(find_pos (Lab l1 l2) labs) -
            &(pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.config.encode (Loc reg tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Loc reg tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ Q.EXISTS_TAC `l'` \\ fs[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][] \\ metis_tac[]
QED

Theorem IMP_bytes_in_memory_Inst:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Asmi(Inst i)) bytes len)) ==>
    ?bytes.
      enc_with_nop mc_conf.target.config.encode (Inst i) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      bytes_in_mem ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain s1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Inst i) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ Q.EXISTS_TAC `l` \\ fs[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ qexists_tac `n` \\ fs[]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][]
QED

Theorem IMP_bytes_in_memory_CallFFI:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (CallFFI name) l bytes n)) ==>
    ?tt enc.
      (tt = -&(pos_val s1.pc 0 code2 + (3 + get_ffi_index ffi_names (ExtCall name)) * ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Theorem IMP_bytes_in_memory_Halt:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm Halt l bytes n)) ==>
    ?tt enc.
      (tt = -&(pos_val s1.pc 0 code2 + ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Theorem bytes_in_mem_IMP_memory:
  !xs a.
      (!a. ~(a IN dm1) ==> m a = m1 a) ==>
      bytes_in_mem a xs m dm dm1 ==>
      bytes_in_memory a xs m1 dm
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_memory_def,bytes_in_mem_def]
QED

Theorem read_bytearray_state_rel:
  !n a x.
      state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
      (read_bytearray a n (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) ==>
      (read_bytearray a n
        (\a. if a IN mc_conf.prog_addresses then SOME (t1.mem a) else NONE) =
       SOME x)
Proof
  Induct
  \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux s1.mem s1.mem_domain s1.be a` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `read_bytearray (a + 1w) n (mem_load_byte_aux s1.mem s1.mem_domain s1.be)` \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def,mem_load_byte_aux_def]
  \\ Cases_on `s1.mem (byte_align a)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ FIRST_X_ASSUM (Q.SPEC_THEN `a` mp_tac) \\ full_simp_tac(srw_ss())[]
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[word_loc_val_def]
  \\ rev_full_simp_tac(srw_ss())[word_loc_val_byte_def,word_loc_val_def]
QED

Theorem IMP_has_io_name:
  (asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    has_io_name index s1.code
Proof
  full_simp_tac(srw_ss())[asm_fetch_def]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`)
  \\ Q.SPEC_TAC (`s1.code`,`code`)
  \\ HO_MATCH_MP_TAC asm_code_length_ind \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,has_io_name_def] \\ res_tac
  \\ Cases_on `is_Label y` \\ full_simp_tac(srw_ss())[]
  THEN1 (Cases_on `y` \\ full_simp_tac(srw_ss())[is_Label_def] \\ res_tac)
  \\ Cases_on `pc = 0` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem bytes_in_mem_asm_write_bytearray_lemma:
  !xs p.
      (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
      bytes_in_mem p xs m1 d k ==>
      bytes_in_mem p xs m2 d k
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def]
QED

Theorem bytes_in_mem_asm_write_bytearray:
  (∀a. byte_align a ∈ s1.mem_domain ⇒ a ∈ s1.mem_domain) ∧
    (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) ==>
    bytes_in_mem p xs t1.mem t1.mem_domain s1.mem_domain ==>
    bytes_in_mem p xs
      (asm_write_bytearray c1 new_bytes t1.mem) t1.mem_domain s1.mem_domain
Proof
  STRIP_TAC \\ match_mp_tac bytes_in_mem_asm_write_bytearray_lemma
  \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`c1`,`a`)
  \\ Q.SPEC_TAC (`x`,`x`)
  \\ Q.SPEC_TAC (`t1.mem`,`m`)
  \\ Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[asm_write_bytearray_def]
  \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ res_tac
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ full_simp_tac(srw_ss())[mem_load_byte_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ srw_tac[][combinTheory.APPLY_UPDATE_THM]
  \\ full_simp_tac(srw_ss())[] \\ res_tac
QED

Theorem write_bytearray_NOT_Loc:
  !xs c1 s1 a c.
      (s1.mem a = Word c) ==>
      (write_bytearray c1 xs s1.mem s1.mem_domain s1.be) a <> Loc n n0
Proof
  Induct \\ full_simp_tac(srw_ss())[write_bytearray_def,mem_store_byte_aux_def]
  \\ rpt strip_tac \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[labSemTheory.upd_mem_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
QED

Theorem CallFFI_bytearray_lemma:
  byte_align (a:'a word) IN s1.mem_domain /\ good_dimindex (:'a) /\
    a IN t1.mem_domain /\
    a IN s1.mem_domain /\
    (s1.be = mc_conf.target.config.big_endian) /\
    (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) /\
    (word_loc_val_byte p labs s1.mem a mc_conf.target.config.big_endian =
       SOME (t1.mem a)) ==>
    (word_loc_val_byte p labs (write_bytearray c1 new_bytes s1.mem s1.mem_domain s1.be) a
       mc_conf.target.config.big_endian =
     SOME (asm_write_bytearray c1 new_bytes t1.mem a))
Proof
  Q.SPEC_TAC (`s1`,`s1`) \\ Q.SPEC_TAC (`t1`,`t1`) \\ Q.SPEC_TAC (`c1`,`c1`)
  \\ Q.SPEC_TAC (`x`,`x`) \\ Q.SPEC_TAC (`new_bytes`,`xs`) \\ Induct
  \\ full_simp_tac(srw_ss())[asm_write_bytearray_def,write_bytearray_def,read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux s1.mem s1.mem_domain s1.be c1` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `read_bytearray (c1 + 1w) (LENGTH xs) (mem_load_byte_aux s1.mem s1.mem_domain s1.be)`
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ qmatch_assum_rename_tac
       `read_bytearray (c1 + 1w) (LENGTH xs) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME y`
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y`,`c1+1w`,`t1`,`s1`])
  \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[mem_store_byte_aux_def]
  \\ reverse (Cases_on `(write_bytearray (c1 + 1w)
       xs s1.mem s1.mem_domain mc_conf.target.config.big_endian) (byte_align c1)`)
  \\ full_simp_tac(srw_ss())[] THEN1
   (full_simp_tac(srw_ss())[mem_load_byte_aux_def]
    \\ Cases_on `s1.mem (byte_align c1)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac write_bytearray_NOT_Loc \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
  \\ `byte_align c1 IN s1.mem_domain` by
    (full_simp_tac(srw_ss())[mem_load_byte_aux_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[labSemTheory.upd_mem_def,word_loc_val_byte_def,APPLY_UPDATE_THM]
  \\ Cases_on `a = c1` \\ full_simp_tac(srw_ss())[word_loc_val_def,good_dimindex_get_byte_set_byte]
  \\ Cases_on `byte_align c1 = byte_align a` \\ full_simp_tac(srw_ss())[word_loc_val_def]
  \\ full_simp_tac(srw_ss())[get_byte_set_byte_diff]
QED

Theorem word_cmp_lemma:
  state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
    (word_cmp cmp (read_reg rr s1) (reg_imm ri s1) = SOME x) ==>
    (x = word_cmp cmp (read_reg rr t1) (reg_imm ri t1))
Proof
  Cases_on `ri` \\ full_simp_tac(srw_ss())[labSemTheory.reg_imm_def,asmSemTheory.reg_imm_def]
  \\ full_simp_tac(srw_ss())[asmSemTheory.read_reg_def]
  \\ Cases_on `s1.regs rr` \\ full_simp_tac(srw_ss())[]
  \\ TRY (Cases_on `s1.regs n`) \\ full_simp_tac(srw_ss())[] \\ Cases_on `cmp`
  \\ full_simp_tac(srw_ss())[wordSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ qpat_x_assum `!bn. bn < _ ==> ~(MEM _ _)` kall_tac
  \\ first_x_assum (kall_tac o Q.SPEC `rr:num`)
  \\ first_assum (assume_tac o Q.SPEC `rr:num`)
  \\ first_x_assum (assume_tac o Q.SPEC `n:num`)
  \\ rev_full_simp_tac(srw_ss())[word_loc_val_def] \\ srw_tac[][]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rpt (qpat_x_assum `1w = xxx` (fn th => full_simp_tac(srw_ss())[GSYM th]))
  \\ rpt (qpat_x_assum `p + n2w xxx = t1.regs rr` (fn th => full_simp_tac(srw_ss())[GSYM th]))
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ metis_tac[EVEN_add_AND]
QED

Theorem list_add_if_fresh_simp:
  !n s. list_add_if_fresh s l =
    if find_index s l n = NONE then
      APPEND l [s]
    else l
Proof
  Induct_on `l`
  >- fs [list_add_if_fresh_def, find_index_def]
  >-
    (rpt strip_tac
     >> FIRST_X_ASSUM (fn thm => ASSUME_TAC(Q.SPEC `n+1` thm))
     >> FIRST_X_ASSUM (fn thm => ASSUME_TAC(Q.SPEC `s` thm))
     >> fs [list_add_if_fresh_def, find_index_def]
     >> every_case_tac
     >> fs [list_add_if_fresh_def, find_index_def])
QED

val list_add_if_fresh_simp = Q.SPECL [`n`,`s`] list_add_if_fresh_simp;

Theorem find_index_append:
  !n. find_index s (l++l') n =
  (case find_index s l n of NONE => find_index s l' (n + LENGTH l) | SOME i => SOME i)
Proof
  Induct_on `l`
  >- fs [find_index_def]
  >-
  (rpt strip_tac
   >> FIRST_X_ASSUM (fn thm => ASSUME_TAC(Q.SPEC `n+1` thm))
   >> fs [find_index_def]
   >> every_case_tac
   >> fs [find_index_def,ADD1])
QED

Theorem has_io_name_find_index:
  !l s. has_io_name s l
  ==> ?y. find_index (ExtCall s) (find_ffi_names l) 0 = SOME y
Proof
  ho_match_mp_tac find_ffi_names_ind
  >> rpt strip_tac
  >> fs[has_io_name_def,find_index_def, find_ffi_names_def,Q.INST [`n`|->`0`] list_add_if_fresh_simp,find_index_append]
  >> every_case_tac
  >> fs[has_io_name_def,find_index_def, find_ffi_names_def,Q.INST [`n`|->`0`] list_add_if_fresh_simp,find_index_append]
  >> every_case_tac
  >> fs[has_io_name_def,find_index_def, find_ffi_names_def,Q.INST [`n`|->`0`] list_add_if_fresh_simp,find_index_append]
  >- metis_tac [NOT_NONE_SOME]
  >- (Cases_on `find_index (ExtCall s) (find_ffi_names (Section k xs::rest)) 0`
      >> metis_tac [NOT_NONE_SOME])
QED

Theorem i2w_sub_nat:
  (i2w (&m - &n):'a word) = n2w m - n2w n
Proof
  rw [integerTheory.int_sub,GSYM integer_wordTheory.word_i2w_add,
      GSYM integer_wordTheory.MULT_MINUS_ONE,integer_wordTheory.i2w_pos]
  \\ metis_tac [WORD_NEG_MUL]
QED

Theorem i2w_neg_nat:
  (i2w (-&n):'a word) = -n2w n
Proof
  rw [GSYM integer_wordTheory.MULT_MINUS_ONE,integer_wordTheory.i2w_pos]
  \\ metis_tac [WORD_NEG_MUL]
QED

val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "lab simulation helper assumptions")
  [enc_with_nop_thm,
   lab_lookup_IMP,
   prog_to_bytes_lemma,
   bytes_in_mem_APPEND,
   IMP_bytes_in_memory,
   IMP_bytes_in_memory_JumpReg,
   IMP_bytes_in_memory_Jump,
   IMP_bytes_in_memory_JumpCmp,
   IMP_bytes_in_memory_JumpCmp_1,
   IMP_bytes_in_memory_Call,
   IMP_bytes_in_memory_LocValue,
   IMP_bytes_in_memory_Inst,
   IMP_bytes_in_memory_CallFFI,
   IMP_bytes_in_memory_Halt,
   bytes_in_mem_IMP_memory,
   read_bytearray_state_rel,
   IMP_has_io_name,
   bytes_in_mem_asm_write_bytearray_lemma,
   bytes_in_mem_asm_write_bytearray,
   write_bytearray_NOT_Loc,
   CallFFI_bytearray_lemma,
   word_cmp_lemma,
   list_add_if_fresh_simp,
   find_index_append,
   has_io_name_find_index,
   i2w_sub_nat,
   i2w_neg_nat];
