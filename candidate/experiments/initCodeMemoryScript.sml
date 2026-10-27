(* Bridge byte installation to the compiler's separated code predicates. *)
Theory initCodeMemory
Ancestors initInitialCode targetSem asmProps
Libs preamble wordsLib
open wordsTheory miscTheory asmPropsTheory targetSemTheory;
Theorem bytes_in_mem_from_elements:
  !bytes a bytesAt byteDomain dataDomain.
    (!i. i < LENGTH bytes ==>
      bytesAt (a+n2w i) = EL i bytes /\ a+n2w i IN byteDomain /\
      a+n2w i NOTIN dataDomain) ==>
    bytes_in_mem a bytes bytesAt byteDomain dataDomain
Proof
  Induct >> rw [bytes_in_mem_def] >>
  TRY (first_x_assum (qspec_then `0` mp_tac) >> simp [] >> NO_TAC) >>
  qpat_x_assum `!a bytesAt byteDomain dataDomain. _` irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  fs [ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
QED
Theorem installed_bytes_separated:
  bytes_in_memory a bytes m byteDomain /\
  (!i. i < LENGTH bytes ==> a+n2w i NOTIN dataDomain) ==>
  bytes_in_mem a bytes m byteDomain dataDomain
Proof
  strip_tac >> irule bytes_in_mem_from_elements >>
  metis_tac [bytes_in_memory_EL,bytes_in_memory_in_domain]
QED
Theorem installed_bytes_read:
  !bytes a.
  bytes_in_memory a bytes m byteDomain ==>
  read_bytearray a (LENGTH bytes)
    (\x. if x IN byteDomain then SOME (m x) else NONE) = SOME bytes
Proof
  Induct >> rw [bytes_in_memory_def,read_bytearray_def] >> fs []
QED
Theorem installed_code_loaded:
  target_state_rel mc.target t ms /\ t.mem_domain = mc.prog_addresses /\
  bytes_in_memory t.pc bytes t.mem t.mem_domain ==>
  code_loaded bytes mc ms
Proof
  rw [code_loaded_def,target_state_rel_def] >>
  ` (\a. if a IN mc.prog_addresses then SOME (mc.target.get_byte ms a) else NONE) =
    (\a. if a IN mc.prog_addresses then SOME (t.mem a) else NONE)` by
    (rw [FUN_EQ_THM] >> fs []) >>
  simp [] >> metis_tac [installed_bytes_read]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "code memory assumptions")
  [bytes_in_mem_from_elements,installed_bytes_separated,installed_bytes_read,
   installed_code_loaded];
