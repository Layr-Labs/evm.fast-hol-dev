(* Instantiate Pancake refinement for the fixed baseline and source state. *)
Theory initBaselineRefinement
Ancestors initBaselineLimits initChallengePancake initSourceAllocation initSourceOrder
Libs preamble wordsLib
open initBaselineLimitsTheory initBaselineInstalledTheory initBackendConfigTheory
  initMachineConfigTheory initCompilerMachineTheory initSubmissionTheory
  initMachineTheory initCompilationInputTheory initSourceTheory initParamsTheory
  initSourceAllocationTheory initSourceOrderTheory initGlobalLayoutTheory
  initChallengePancakeTheory initChallengeSemanticsTheory
  targetSemTheory backendProofTheory backendTheory riscv_targetTheory wordsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = metisTools.limit := {time=SOME 10.0,infs=NONE};
Theorem compiler_target_config:
  (compilerMachineConfig candidateSubmission).target.config = riscv_config
Proof
  simp [compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
        restrictedTarget_def,riscv_target_def]
QED
Theorem compiler_mc_conf_ok:
  lab_to_targetProof$mc_conf_ok (compilerMachineConfig candidateSubmission)
Proof
  `lab_to_targetProof$mc_conf_ok (compilerMachineConfig candidateSubmission) =
   lab_to_targetProof$mc_conf_ok (submissionConfig candidateSubmission)` by
    simp [compilerMachineConfig_def,lab_to_targetProofTheory.mc_conf_ok_def] >>
  simp [submissionConfig_def,challenge_machine_config_ok]
QED
Theorem compiler_mc_init_ok:
  mc_init_ok riscv_config (set_oracle guestConfig allocation)
    (compilerMachineConfig candidateSubmission)
Proof
  `mc_init_ok riscv_config (set_oracle guestConfig allocation)
     (compilerMachineConfig candidateSubmission) =
   mc_init_ok riscv_config (set_oracle guestConfig allocation)
     (submissionConfig candidateSubmission)` by
    simp [compilerMachineConfig_def,mc_init_ok_def] >>
  simp [submissionConfig_def] >>
  irule (SIMP_RULE (srw_ss()) [] guest_machine_initial_config_ok)
QED
Theorem baseline_source_addresses:
  ordinaryDomain = addresses (n2w sourceBase:word64)
    ((stackStart-sourceBase) DIV 8 - globalsWords)
Proof
  rewrite_tac [ordinaryDomain_def,stack_removeProofTheory.addresses_thm,
               byteTheory.bytes_in_word_def] >>
  simp_tac std_ss [dimindex_64,word_mul_n2w,MULT_COMM]
QED
val baseline_compile_rule = Q.GENL
  [`s`,`mc`,`c`,`c'`,`pan_code`,`bytes`,`bitmaps`,`stack_max`,`ffi`,
   `globals_size`,`heap_len`,`adj_ptr2`,`adj_ptr4`,`cbspace`,`data_sp`,`start`]
  challenge_pan_to_target_compile_semantics;
Theorem baseline_native_refinement:
  target_state_rel restrictedTarget (bootFinalState (baselineInitialAsm input)) ms /\
  sourceBehaviour input <> Fail ==>
  challengeMachineSem (compilerMachineConfig baselineSubmission)
    (sourceFfi input) ms SUBSET {sourceBehaviour input}
Proof
  strip_tac >> drule baseline_bounded_compilation >> strip_tac >>
  mp_tac (Q.ISPECL
    [`sourceInitialState input`,`compilerMachineConfig baselineSubmission`,
     `set_oracle guestConfig allocation`,`c:backend$config`,`prepared_guest`,
     `compiledBytes`,`compiledBitmaps`,`SOME (depth:num)`,`sourceFfi input`,
     `globalsWords`,`(stackStart-sourceBase) DIV 8`,
     `(n2w sourceBase:word64) + bytes_in_word * n2w stack_remove$max_stack_alloc`,
     `(n2w ramEnd:word64) - bytes_in_word * n2w stack_remove$max_stack_alloc`,
     `760:num`,`0:num`,`«main»`] baseline_compile_rule) >>
  simp [compiler_target_config,prepared_fixed_source_behaviour,
        semanticsPropsTheory.extend_with_resource_limit'_def] >>
  impl_tac >-
    (simp [prepared_source_premises,compiler_mc_conf_ok,compiler_mc_init_ok,
           guest_backend_config_ok,prepared_globals_match_source,LET_THM,
           source_oracle_fixed] >>
     simp [SIMP_RULE (srw_ss()) [] prepared_source_premises,
           SIMP_RULE (srw_ss()) [] guest_backend_config_ok,
           SIMP_RULE (srw_ss()) [] compiler_mc_init_ok] >>
     `heap_regs guestConfig.stack_conf.reg_names = (11,13)` by EVAL_TAC >>
     imp_res_tac baseline_pan_installed >> imp_res_tac baseline_native_registers >>
     simp [sourceInitialState_def,sourceInitialStateFor_def] >>
     simp [compilerMachineConfig_def,submissionConfig_def,challengeMachineConfig_def,
           restrictedTarget_def,riscv_target_def,riscv_config_def] >>
     rewrite_tac [REWRITE_RULE [sourceBase_def] baseline_source_addresses] >>
     simp [set_oracle_def,guestConfig_def,pancakeRiscvConfig_def] >>
     rewrite_tac [sourceBase_def] >> EVAL_TAC) >>
  fs [pan_to_targetProofTheory.option_lt_def]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline refinement assumptions")
  [compiler_target_config,compiler_mc_conf_ok,compiler_mc_init_ok,
   baseline_source_addresses,baseline_native_refinement];
