(* Admission fixes the external-call/MMIO boundary used by the compiler. *)
Theory initFfiBoundary
Ancestors initFfiInstallation
Libs preamble
open targetSemTheory initSubmissionTheory;
Theorem ffi_boundary_shape:
  ffiNameBoundaryValid names nexternal ==>
  nexternal <= LENGTH names /\
  (!j. j < nexternal ==> ?name. EL j names = ExtCall name) /\
  (!j. nexternal <= j /\ j < LENGTH names ==> ?op. EL j names = SharedMem op)
Proof
  strip_tac >> `nexternal <= LENGTH names` by fs [ffiNameBoundaryValid_def] >>
  simp [] >> conj_tac >> rpt strip_tac >>
  `j < LENGTH names` by decide_tac >>
  qpat_x_assum `ffiNameBoundaryValid _ _` mp_tac >>
  rw [ffiNameBoundaryValid_def] >>
  first_x_assum (qspec_then `j` mp_tac) >> Cases_on `EL j names` >> fs []
QED
Theorem ffi_boundary_exists:
  ffiNameBoundaryValid names nexternal ==> ?i. mmio_pcs_min_index names = SOME i
Proof
  strip_tac >> drule ffi_boundary_shape >> strip_tac >>
  rewrite_tac [mmio_pcs_min_index_def] >>
  DEEP_INTRO_TAC optionTheory.some_intro >> simp [] >> metis_tac []
QED
Theorem ffi_boundary_exact:
  ffiNameBoundaryValid names nexternal ==> mmio_pcs_min_index names = SOME nexternal
Proof
  metis_tac [ffi_boundary_exists,admitted_name_boundary_unique]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "FFI boundary assumptions")
  [ffi_boundary_shape,ffi_boundary_exists,ffi_boundary_exact];
