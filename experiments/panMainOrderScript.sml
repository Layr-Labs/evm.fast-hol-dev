(* Moving one function declaration past declarations of other names. *)
Theory panMainOrder
Ancestors panProps
Libs preamble
open panLangTheory panSemTheory finite_mapTheory;
Theorem evaluate_function_swap:
  ~MEM fi.name (MAP FST (functions [d])) ==>
  evaluate_decls s (Function fi::d::ds) =
  evaluate_decls s (d::Function fi::ds)
Proof
  Cases_on `d` >> simp [functions_def] >>
  TRY (MATCH_ACCEPT_TAC evaluate_decl_commute) >>
  rw [evaluate_decls_def,FUPDATE_COMMUTES]
QED
Theorem evaluate_decls_cons_cong:
  (!t : ('a,'ffi) panSem$state. evaluate_decls t xs = evaluate_decls t ys) ==>
  evaluate_decls (s : ('a,'ffi) panSem$state) (d::xs) = evaluate_decls s (d::ys)
Proof
  strip_tac >>
  `d::xs = [d] ++ xs` by simp [] >>
  `d::ys = [d] ++ ys` by simp [] >>
  asm_simp_tac std_ss [] >> rewrite_tac [evaluate_decls_append] >>
  TOP_CASE_TAC >> simp [] >> metis_tac []
QED
Theorem evaluate_function_move:
  !ds s fi.
    ~MEM fi.name (MAP FST (functions ds)) ==>
    evaluate_decls s (Function fi::ds) =
    evaluate_decls s (ds ++ [Function fi])
Proof
  Induct_on `ds` >> simp [] >> rpt gen_tac >> strip_tac >>
  `~MEM fi.name (MAP FST (functions [h])) /\
   ~MEM fi.name (MAP FST (functions ds))` by
    (Cases_on `h` >> fs [functions_def]) >>
  asm_simp_tac std_ss [Once evaluate_function_swap] >>
  irule evaluate_decls_cons_cong >> fs []
QED
Theorem decs_stcnames_append_function:
  !ds ctxt fi.
    decs_stcnames ctxt (ds ++ [Function fi]) = decs_stcnames ctxt ds
Proof
  Induct_on `ds` >> simp [decs_stcnames_def] >>
  rpt gen_tac >> Cases_on `h` >> simp [decs_stcnames_def] >>
  rpt (TOP_CASE_TAC >> simp []) >> fs []
QED
Theorem semantics_function_move:
  ~MEM fi.name (MAP FST (functions ds)) ==>
  semantics_decls s start (Function fi::ds) =
  semantics_decls s start (ds ++ [Function fi])
Proof
  strip_tac >>
  simp [semantics_decls_def,decs_stcnames_def,decs_stcnames_append_function] >>
  TOP_CASE_TAC >> simp [evaluate_function_move]
QED
val _ = List.app (fn th =>
  if null (hyp th) then ignore (check_thm th) else failwith "reordering assumptions")
  [evaluate_function_swap,evaluate_decls_cons_cong,evaluate_function_move,
   decs_stcnames_append_function,semantics_function_move];
