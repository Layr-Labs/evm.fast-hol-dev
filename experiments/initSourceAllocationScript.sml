(* Discharge global allocation against the challenge's fixed source memory. *)
Theory initSourceAllocation
Ancestors initGlobalLayout
Libs preamble wordsLib
open initParamsTheory initSourceTheory pan_to_wordProofTheory
  stack_removeProofTheory;
val layout_defs = [sourceBase_def,stackStart_def,ramEnd_def,ramStart_def,
  ramSize_def,stackSize_def,globalsWords_def,heapEnd_def];
Theorem ordinary_below_globals:
  (x : word64) IN ordinaryDomain ==> w2n x < heapEnd
Proof
  rw [ordinaryDomain_def] >>
  fs (layout_defs @ [word_add_n2w,w2n_n2w,dimword_64]) >>
  intLib.COOPER_TAC
QED
Theorem globals_above_ordinary:
  (x : word64) IN addresses (n2w heapEnd) globalsWords ==>
  heapEnd <= w2n x
Proof
  rw [addresses_thm] >>
  fs (layout_defs @ [byteTheory.bytes_in_word_def,
    word_mul_n2w,word_add_n2w,w2n_n2w,dimword_64]) >>
  intLib.COOPER_TAC
QED
Theorem globals_end_outside_ordinary:
  ~((n2w heapEnd + bytes_in_word * n2w globalsWords : word64)
     IN ordinaryDomain)
Proof
  strip_tac >> drule ordinary_below_globals >>
  simp (layout_defs @ [byteTheory.bytes_in_word_def,
    word_mul_n2w,word_add_n2w,w2n_n2w,dimword_64])
QED
val globals_size_empty = SIMP_RULE (srw_ss())
  [initGlobalLayoutTheory.prepared_struct_context]
  initGlobalLayoutTheory.prepared_globals_match_source;
Theorem prepared_globals_allocatable:
  globals_allocatable (sourceInitialState input) prepared_guest
Proof
  rewrite_tac [globals_allocatable_def,LET_THM] >>
  rewrite_tac [initGlobalLayoutTheory.prepared_globals_match_source] >>
  simp [initGlobalLayoutTheory.prepared_struct_context,
    sourceInitialState_def,sourceInitialStateFor_def,
    globals_end_outside_ordinary] >>
  simp [globals_size_empty,globals_end_outside_ordinary] >>
  conj_tac
  >- (simp [pred_setTheory.DISJOINT_DEF,pred_setTheory.EXTENSION] >>
      metis_tac [ordinary_below_globals,globals_above_ordinary,
        arithmeticTheory.NOT_LESS_EQUAL]) >>
  simp (layout_defs @ [byteTheory.bytes_in_word_def,dimword_64])
QED
Theorem prepared_source_premises:
  pancake_good_code prepared_guest /\
  distinct_params (functions prepared_guest) /\
  ALL_DISTINCT (MAP FST (functions prepared_guest)) /\
  size_of_eids prepared_guest < dimword (:64) /\
  globals_allocatable (sourceInitialState input) prepared_guest /\
  (sourceInitialState input).code = FEMPTY /\
  (sourceInitialState input).locals = FEMPTY /\
  (sourceInitialState input).globals = FEMPTY /\
  (sourceInitialState input).eshapes = FEMPTY
Proof
  simp [initSourceChecksTheory.prepared_good_code,
    initSourceChecksTheory.prepared_distinct_params,
    initSourceChecksTheory.prepared_distinct_functions,
    initSourceChecksTheory.prepared_exception_bound,
    prepared_globals_allocatable] >>
  simp [sourceInitialState_def,sourceInitialStateFor_def]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "allocation assumptions")
  [ordinary_below_globals,globals_above_ordinary,globals_end_outside_ordinary,
   prepared_globals_allocatable,prepared_source_premises];
