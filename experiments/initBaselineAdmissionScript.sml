(* Admission of the exact compiled baseline, with fixed sanitized metadata. *)
Theory initBaselineAdmission
Ancestors initBaselineRom initCompiledMetadata initSubmission
Libs preamble cv_transLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
fun save_closed name th =
  if null (hyp th) then save_thm (name,check_thm th)
  else failwith (name ^ " has assumptions");
Theorem bounded_all[cv_inline]:
  (!i:num. i < n ==> P i) = EVERY (\i. if i < n then P i else T) (GENLIST I n)
Proof
  simp [EVERY_MEM,MEM_GENLIST] >> metis_tac []
QED
Theorem bounded_all_guard[cv_inline]:
  (!i:num. i < n /\ Q i ==> P i) =
    EVERY (\i. if i < n then (if Q i then P i else T) else T) (GENLIST I n)
Proof
  simp [EVERY_MEM,MEM_GENLIST] >> metis_tac []
QED
Theorem member_all[cv_inline]:
  (!x. MEM x xs ==> P x) = EVERY P xs
Proof
  simp [EVERY_MEM]
QED
Definition baselineExtra_def:
  baselineExtra = MAP (\r : lab_to_target$shmem_info_num.
    init_mmio r.entry_pc r.nbytes r.addr_reg (Num r.addr_off) r.reg r.exit_pc)
    compiledMmio
End
val _ = cv_auto_trans baselineExtra_def;
Definition baselineMetadataRoundtrip_def:
  baselineMetadataRoundtrip =
    (MAP (\r : init_mmio.
      (<| entry_pc := r.entry_pc; nbytes := r.nbytes; addr_reg := r.addr_reg;
          addr_off := &r.addr_off; reg := r.reg; exit_pc := r.exit_pc |>
         : lab_to_target$shmem_info_num)) baselineExtra = compiledMmio)
End
val _ = cv_auto_trans baselineMetadataRoundtrip_def;
val _ = save_closed "baseline_metadata_roundtrip"
  (EQT_ELIM (cv_eval ``baselineMetadataRoundtrip``));
Definition baselineSubmission_def:
  baselineSubmission = submission baselineRom baselineNativePc
    compiledFfiNames compiledFirst baselineExtra
End
val _ = cv_auto_trans baselineSubmission_def;
(* Evaluate only the observable layout projections, rather than translating
   the machine configuration's higher-order execution functions. *)
val bounded_rewrite = CONV_RULE
  (DEPTH_CONV (FIRST_CONV (map HO_REWR_CONV
    [bounded_all_guard,bounded_all,member_all])) THENC DEPTH_CONV BETA_CONV);
val names_literal = cv_eval ``compiledFfiNames``;
val extra_literal = cv_eval ``baselineExtra``;
val first_literal = cv_eval ``compiledFirst``;
val _ = List.app print_thm [initCompiledMetadataTheory.compiled_ffi_count,
  initCompiledMetadataTheory.compiled_mmio_count,first_literal];
val admission_reduced = REWRITE_CONV
  [admitted_def,baselineSubmission_def,submissionConfig_def,
   initMachineTheory.challengeMachineConfig_def,programDomain_def,
   ffiNameBoundaryValid_def,initBaselineRomTheory.baseline_rom_length,
   names_literal,extra_literal,first_literal] ``admitted baselineSubmission``
  |> bounded_rewrite
  |> SIMP_RULE (srw_ss()) [initBaselineRomTheory.baseline_rom_length]
  |> bounded_rewrite;
val admission_result = TRANS admission_reduced (EVAL (rhs (concl admission_reduced)));
val _ = save_closed "baseline_admitted" (EQT_ELIM admission_result);

val spacing = REWRITE_CONV [initBootstrapTheory.bootstrap_size,first_literal]
  ``initialPc + LENGTH bootstrapBytes <
    baselineNativePc - ffiOffset * (compiledFirst + 2)``;
val _ = save_closed "bootstrap_before_dispatch_slots"
  (EQT_ELIM (TRANS spacing (EVAL (rhs (concl spacing)))));
