(* A factored byte-memory view of the bootstrap's little-endian stores. *)
Theory initBootstrapStores
Ancestors initBootstrapMemory
Libs preamble wordsLib
open asmSemTheory wordsTheory;
Definition littleStore_def:
  littleStore 0 (a:word64) (w:word64) (bytesAt:word64 -> word8) = bytesAt /\
  littleStore (SUC n) a w bytesAt =
    (a =+ w2w w) (littleStore n (a+1w) (w >>> 8) bytesAt)
End
Theorem write_word_memory:
  !n a w (s:64 asm_state). ~s.be ==>
    (write_mem_word a n w s).mem = littleStore n a w s.mem
Proof
  Induct >> simp [write_mem_word_def,littleStore_def,assert_def,upd_mem_def]
QED
Theorem store_memory:
  ~(s:64 asm_state).be ==>
    (mem_store n rn a s).mem =
    littleStore n (addr a s) (s.regs rn) s.mem
Proof
  simp [mem_store_def,assert_def,read_reg_def,write_word_memory]
QED
Theorem little_store_selected:
  !j. j < 8 ==>
    littleStore 8 a w bytesAt (a+n2w j) = (w2w (w >>> (8*j)) : word8)
Proof
  mp_tac (Q.INST [`s` |-> `(s:64 asm_state) with <|be := F; mem := bytesAt|>`]
    write_word_selected) >> simp [write_word_memory]
QED
Theorem little_store_outside:
  (!j. j < 8 ==> x <> a+n2w j) ==>
    littleStore 8 a w bytesAt x = bytesAt x
Proof
  mp_tac (Q.INST [`s` |-> `(s:64 asm_state) with <|be := F; mem := bytesAt|>`]
    write_word_outside) >> simp [write_word_memory]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "store assumptions")
  [write_word_memory,store_memory,little_store_selected,little_store_outside];
