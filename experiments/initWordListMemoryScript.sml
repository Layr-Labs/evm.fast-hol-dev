(* Build the compiler's separated word list from indexed memory facts. *)
Theory initWordListMemory
Ancestors stack_removeProof
Libs preamble wordsLib
open wordsTheory miscTheory set_sepTheory stack_removeProofTheory;
Theorem indexed_word_list_memory:
  good_dimindex (:'a) /\
  w2n (a:'a word) + LENGTH xs * w2n (bytes_in_word:'a word) < dimword (:'a) /\
  (!i. i < LENGTH xs ==> m (a+n2w i*bytes_in_word) = EL i xs) ==>
  word_list a xs
    (fun2set (m, IMAGE (\i. a+n2w i*bytes_in_word) (count (LENGTH xs))))
Proof
  strip_tac >>
  drule_all word_list_seteq >> disch_then (fn th => rewrite_tac [th]) >>
  fs [EXTENSION,fun2set_def,MEM_GENLIST] >> metis_tac []
QED
val _ = if null(hyp indexed_word_list_memory)
  then ignore(check_thm indexed_word_list_memory)
  else failwith "indexed word list assumptions";
