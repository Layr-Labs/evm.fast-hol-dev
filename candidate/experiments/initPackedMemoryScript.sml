(* A total word-memory view of the actual machine bytes. *)
Theory initPackedMemory
Ancestors initBootstrapSourceMemory wordLang
Libs preamble wordsLib
open wordsTheory byteTheory alignmentTheory initBootstrapSourceMemoryTheory;
Theorem packed_word_byte:
  j < 8 ==>
  get_byte (n2w j) (packedBootWord bytesAt a) F = bytesAt (a+n2w j)
Proof
  simp_tac std_ss [packedBootWord_def,get_byte_word_of_bytes_le,
    first_byte_at_0w,dimword_64,dimindex_64,LENGTH_GENLIST,EL_GENLIST]
QED
Theorem byte_align_offset:
  byte_align (a:word64) + n2w (w2n a MOD 8) = a
Proof
  simp [byte_align_def,align_w2n,word_add_n2w] >>
  metis_tac [DIVISION,DECIDE ``0 < 8:num``,n2w_w2n,MULT_COMM]
QED
Theorem packed_memory_byte:
  get_byte a (packedBootWord bytesAt (byte_align a)) F = bytesAt a
Proof
  once_rewrite_tac [GSYM (SIMP_RULE (srw_ss()) []
    (INST_TYPE [alpha |-> ``:64``] get_byte_cycle))] >>
  simp [packed_word_byte,byte_align_offset]
QED
Definition packedMemory_def:
  packedMemory bytesAt address : 64 word_loc =
    wordLang$Word (packedBootWord bytesAt address)
End
Theorem packed_memory_relation:
  !a. ?w. bytesAt a = get_byte a w F /\
           packedMemory bytesAt (byte_align a) = wordLang$Word w
Proof
  rw [packedMemory_def] >> metis_tac [packed_memory_byte]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "packed memory assumptions")
  [packed_word_byte,byte_align_offset,packed_memory_byte,packed_memory_relation];
