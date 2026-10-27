(* The fixed challenge callbacks satisfy CakeML's FFI calling convention. *)
Theory initFfiInstallation
Ancestors initMachineReturn initSubmission lab_to_targetProof
Libs preamble wordsLib
open asmSemTheory asmPropsTheory targetSemTheory riscv_targetTheory
  initMachineTheory initSubmissionTheory initMachineReturnTheory
  miscTheory wordsTheory lab_to_targetProofTheory;
Theorem mmio_info_before_boundary:
  index < nexternal ==>
  ALOOKUP (machineMmioInfo pc nexternal extra) index = NONE
Proof
  simp [machineMmioInfo_def,ALOOKUP_ZIP_FAIL,MEM_GENLIST] >>
  rpt strip_tac >> decide_tac
QED
Theorem admitted_name_boundary_unique:
  ffiNameBoundaryValid names nexternal /\
  mmio_pcs_min_index names = SOME i ==> i = nexternal
Proof
  rw [ffiNameBoundaryValid_def] >>
  drule mmio_pcs_min_index_is_SOME >> strip_tac >>
  Cases_on `i < nexternal`
  >- (`i < LENGTH names` by decide_tac >>
      `?op. EL i names = SharedMem op` by metis_tac [LESS_EQ_REFL] >>
      qpat_x_assum `!j. j < LENGTH names ==> _` (qspec_then `i` mp_tac) >> simp []) >>
  Cases_on `nexternal < i`
  >- (`nexternal < LENGTH names` by decide_tac >>
      `?str. EL nexternal names = ExtCall str` by metis_tac [] >>
      qpat_x_assum `!j. j < LENGTH names ==> _` (qspec_then `nexternal` mp_tac) >> simp []) >>
  decide_tac
QED
Theorem admitted_ffi_interference:
  admitted s ==> ffi_interfer_ok pc (submissionConfig s)
Proof
  strip_tac >>
  `ffiNameBoundaryValid s.names s.first` by fs [admitted_def] >>
  simp [ffi_interfer_ok_def,submissionConfig_def,challengeMachineConfig_def] >>
  rpt gen_tac >> strip_tac >>
  `i = s.first` by metis_tac [admitted_name_boundary_unique] >> gvs [] >>
  conj_tac
  >- (rpt strip_tac >>
      simp [machineFfiInterference_def,mmio_info_before_boundary] >>
      fs [restrictedTarget_def,riscv_target_def,riscv_config_def] >>
      drule (SIMP_RULE (srw_ss())
        [restrictedTarget_def,riscv_target_def,riscv_config_def]
        machine_ext_return_relation) >>
      disch_then (qspec_then `new_bytes` mp_tac) >>
      simp [target_state_rel_def] >> metis_tac []) >>
  strip_tac >>
  `mmioRecordValid (n2w s.anchorPc) s.first s.extra index` by
    metis_tac [admitted_def] >>
  fs [mmioRecordValid_def] >>
  Cases_on `ALOOKUP (machineMmioInfo (n2w s.anchorPc) s.first s.extra) index` >>
  fs [] >> PairCases_on `x` >> fs [] >>
  simp [machineFfiInterference_def] >> conj_tac >> strip_tac
  >- (gen_tac >> drule machine_set_reg_pc_relation >> simp [] >>
      disch_then (qspecl_then [`word_of_bytes F 0w new_bytes`,`x2`,`x3`] mp_tac) >>
      simp [machineMmioReturn_def,combinTheory.UPDATE_def,EQ_SYM_EQ]) >>
  drule (SIMP_RULE (srw_ss()) [machineMmioReturn_def] machine_mmio_write_relation) >>
  simp [] >> disch_then (qspec_then `x3` mp_tac) >> simp [machineMmioReturn_def]

QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "FFI installation assumptions")
  [mmio_info_before_boundary,admitted_name_boundary_unique,admitted_ffi_interference];
