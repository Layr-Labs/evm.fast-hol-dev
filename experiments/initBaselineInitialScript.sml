(* Instantiate the bootstrap for the fixed challenge memory and registers. *)
Theory initBaselineInitial
Ancestors initBootstrapFullExecution initNativeInstalled
Libs preamble wordsLib
open asmSemTheory asmPropsTheory wordsTheory riscv_targetTheory
  initParamsTheory initSubmissionTheory initMachineTheory
  initBaselineAdmissionTheory initCompiledMetadataTheory initBaselineRomTheory
  initBootstrapTheory initBootstrapStepTheory initBootstrapStateTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition baselineInitialAsm_def:
  baselineInitialAsm input : 64 asm_state =
    <| regs := (\n. 0w); fp_regs := (\n. 0w);
       mem := initialMemory baselineSubmission input;
       mem_domain := programDomain baselineSubmission;
       pc := n2w initialPc; lr := 1; align := 2; be := F; failed := F |>
End
Theorem baseline_bootstrap_domains:
  (!i. i < 36936 ==>
    n2w (bootDataRom+i) IN programDomain baselineSubmission /\
    n2w (bootDataRam+i) IN programDomain baselineSubmission) /\
  (!i. i < 40 ==> n2w (0xa1000000+i) IN programDomain baselineSubmission)
Proof
  rw [IN_DEF,programDomain_def,submissionMemoryDomain_def,
      submissionSharedDomain_def,baselineSubmission_def,compiled_first,
      baselineNativePc_def,bootDataRom_def,bootDataRam_def,ffiOffset_def,
      initialPc_def,codeSizeLimit_def,ramStart_def,ramEnd_def,ramSize_def,
      inputStart_def,inputEnd_def,inputSize_def,outputStart_def,
      outputEnd_def,outputSize_def,WORD_EQ_SUB_LADD,word_add_n2w,n2w_11,
      w2n_n2w,dimword_64] >> decide_tac
QED
Theorem baseline_initial_target_relation:
  target_state_rel riscv_target (baselineInitialAsm input)
    (initialState baselineSubmission input)
Proof
  simp [target_state_rel_def,riscv_target_def,baselineInitialAsm_def,
        initial_state_valid,riscv_config_def,initial_registers,initial_pc] >>
  simp [initialState_def]
QED
Theorem baseline_bootstrap_execution:
  RTC (\s1 s2. ?instruction. asm_step riscv_config s1 instruction s2)
    (baselineInitialAsm input) (bootFinalState (baselineInitialAsm input))
Proof
  irule initBootstrapFullExecutionTheory.bootstrap_full_execution >>
  simp [baselineInitialAsm_def,bootstrapRomInvariant_def] >>
  metis_tac [baseline_bootstrap_domains,ADD_COMM]
QED
Theorem baseline_native_installed:
  bytes_in_memory (n2w baselineNativePc) initBytecode$compiledBytes
    (bootFinalState (baselineInitialAsm input)).mem
    (bootFinalState (baselineInitialAsm input)).mem_domain
Proof
  irule initNativeInstalledTheory.native_installed_after_bootstrap >>
  simp_tac (srw_ss()) [baselineInitialAsm_def] >>
  qexists_tac `baselineSubmission` >> qexists_tac `input` >>
  simp [baselineInitialAsm_def,baselineSubmission_def,compiled_first,
        initialPc_def,ffiOffset_def,baselineNativePc_def]
QED
Theorem baseline_native_entry:
  (bootFinalState (baselineInitialAsm input)).pc = n2w baselineNativePc /\
  (bootFinalState (baselineInitialAsm input)).regs 10 = n2w baselineNativePc /\
  (bootFinalState (baselineInitialAsm input)).regs 11 = 0xa1000000w /\
  (bootFinalState (baselineInitialAsm input)).regs 12 = 0x7df000000w /\
  (bootFinalState (baselineInitialAsm input)).regs 13 = 0x7e0000000w /\
  ~(bootFinalState (baselineInitialAsm input)).failed
Proof
  mp_tac (Q.INST [`s` |-> `baselineInitialAsm input`] bootstrap_final_effect) >>
  simp [baselineInitialAsm_def] >>
  metis_tac [baseline_bootstrap_domains,ADD_COMM]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "baseline initial state assumptions")
  [baseline_bootstrap_domains,baseline_initial_target_relation,
   baseline_bootstrap_execution,baseline_native_installed,baseline_native_entry];
