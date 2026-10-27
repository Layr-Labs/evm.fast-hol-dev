(* CakeML-derived portions are covered by ../CAKEML-LICENSE. *)
(* Re-export CakeML's proved in-logic backend correspondence for Pancake.
   Proofs copied from the pinned backend_asmScript.sml, where they are local. *)
Theory pancakeBackendBridge
Ancestors backend_asm
Libs preamble
Theorem from_lab_thm:
  from_lab asm_conf c names p bm =
  SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ⇒
  ∃c1.
    backend$from_lab asm_conf c names p bm = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config c1
Proof
  gvs [from_lab_def,backendTheory.from_lab_def]
  \\ gvs [attach_bitmaps_def |> DefnBase.one_line_ify NONE, AllCaseEqs()] \\ rw []
  \\ gvs [compile_lab_def,lab_to_target_def,
          lab_to_targetTheory.compile_def,lab_to_targetTheory.compile_lab_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ pop_assum kall_tac
  \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [backendTheory.attach_bitmaps_def]
QED

Theorem from_stack_thm:
  from_stack asm_conf c names p bm =
  SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ⇒
  ∃c1.
    backend$from_stack asm_conf c names p bm = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config c1
Proof
  gvs [from_stack_def,backendTheory.from_stack_def] \\ rw []
  \\ drule from_lab_thm \\ strip_tac \\ gvs []
QED

Theorem word_to_word_inlogic_thm:
  word_to_word_inlogic asm_conf c.word_to_word_conf p = SOME (col,prog) ⇒
  compile c.word_to_word_conf asm_conf p = (col,prog)
Proof
  gvs [word_to_word_inlogic_def,word_to_wordTheory.compile_def]
  \\ pairarg_tac \\ gvs [AllCaseEqs()] \\ rw []
  \\ last_x_assum kall_tac
  \\ pop_assum mp_tac
  \\ qspec_tac (‘ZIP (p,n_oracles)’,‘xs’)
  \\ qid_spec_tac ‘prog’
  \\ Induct_on ‘xs’
  \\ gvs [each_inlogic_def]
  \\ PairCases
  \\ gvs [each_inlogic_def,AllCaseEqs(),word_alloc_inlogic_def]
  \\ rpt strip_tac \\ gvs []
  \\ gvs [word_to_wordTheory.full_compile_single_def]
  \\ gvs [word_to_wordTheory.compile_single_def]
  \\ rw [] \\ gvs [word_allocTheory.word_alloc_def]
QED

Theorem from_word_0_thm:
  from_word_0 asm_conf (c,p,names) =
  SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ⇒
  ∃c1.
    backend$from_word_0 asm_conf c names p = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config c1
Proof
  gvs [from_word_0_def,from_word_def,AllCaseEqs()] \\ strip_tac \\ gvs []
  \\ gvs [backendTheory.from_word_0_def,backendTheory.from_word_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac word_to_word_inlogic_thm \\ gvs []
  \\ drule from_stack_thm
  \\ strip_tac
  \\ pop_assum $ irule_at Any
  \\ gvs []
QED
