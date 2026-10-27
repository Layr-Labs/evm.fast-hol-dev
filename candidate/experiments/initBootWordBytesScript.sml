(* Recover compiler bitmap words from their exact little-endian ROM bytes. *)
Theory initBootWordBytes
Ancestors initBaselineRom initPackedMemory
Libs preamble wordsLib
open wordsTheory byteTheory initBaselineRomTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Theorem boot_word_bytes_length:
  LENGTH (bootWordBytes w) = 8
Proof
  simp [bootWordBytes_def]
QED
Theorem boot_word_bytes_inverse:
  (word_of_bytes F 0w (bootWordBytes w) : word64) = w
Proof
  irule (SIMP_RULE (srw_ss()) [EVAL ``divides 8 64``]
    (Q.INST [`be` |-> `F`]
      (INST_TYPE [alpha |-> ``:64``] word_eq_of_get_byte))) >>
  rpt strip_tac >>
  asm_simp_tac std_ss [bootWordBytes_def,get_byte_word_of_bytes_le,
    first_byte_at_0w,LENGTH_GENLIST,EL_GENLIST,dimindex_64,dimword_64,
    get_byte_n2w_le] >>
  simp [EXP_EXP_MULT]
QED
Theorem flat_word_bytes_el:
  !ws i j. i < LENGTH ws /\ j < 8 ==>
    EL (8*i+j) (FLAT (MAP bootWordBytes ws)) =
    EL j (bootWordBytes (EL i ws))
Proof
  Induct >> simp [] >> Cases_on `i` >>
  rw [EL_APPEND,boot_word_bytes_length,MULT_CLAUSES,ADD_CLAUSES] >> fs [] >>
  metis_tac [ADD_COMM]
QED
Theorem flat_word_bytes_slice:
  i < LENGTH ws ==>
  GENLIST (\j. EL (8*i+j) (FLAT (MAP bootWordBytes ws))) 8 =
  bootWordBytes (EL i ws)
Proof
  strip_tac >> irule LIST_EQ >>
  simp_tac std_ss [LENGTH_GENLIST,boot_word_bytes_length,EL_GENLIST] >>
  metis_tac [flat_word_bytes_el]
QED
Theorem flat_word_bytes_inverse:
  i < LENGTH ws ==>
  (word_of_bytes F 0w
     (GENLIST (\j. EL (8*i+j) (FLAT (MAP bootWordBytes ws))) 8) : word64) = EL i ws
Proof
  simp [flat_word_bytes_slice,boot_word_bytes_inverse]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "bitmap byte inversion assumptions")
  [boot_word_bytes_length,boot_word_bytes_inverse,flat_word_bytes_el,
   flat_word_bytes_slice,flat_word_bytes_inverse];
