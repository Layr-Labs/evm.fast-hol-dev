(* Valid assembler steps for bootstrap instructions under the ROM invariant. *)
Theory initBootstrapStep
Ancestors initBootstrapInstalled initBootstrapLoop
Libs preamble wordsLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapLoopTheory
  initParamsTheory riscv_targetTheory miscTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition bootstrapRomInvariant_def:
  bootstrapRomInvariant input (s:64 asm_state) =
    (s.mem_domain = programDomain baselineSubmission /\
     !a. w2n a < bootDataRam ==>
       s.mem a = initialMemory baselineSubmission input a)
End
Theorem bootstrap_instruction_bounds:
  MEM (pc,instruction) bootstrapBlocks ==>
  initialPc <= pc /\
  pc + LENGTH (riscv_enc instruction) <= initialPc + LENGTH bootstrapBytes
Proof
  strip_tac >> mp_tac bootstrap_slices >>
  rewrite_tac [bootstrapSlices_def,EVERY_MEM] >>
  disch_then (qspec_then `(pc,instruction)` mp_tac) >> simp []
QED
Theorem bootstrap_fetch_from_frame:
  MEM (pc,instruction) bootstrapBlocks /\ bootstrapRomInvariant input s ==>
  bytes_in_memory (n2w pc) (riscv_enc instruction) s.mem s.mem_domain
Proof
  strip_tac >> imp_res_tac bootstrap_instruction_bounds >>
  fs [bootstrapRomInvariant_def] >>
  irule bytes_in_memory_change_mem >>
  qexists_tac `initialMemory baselineSubmission input` >>
  conj_tac
  >- (rpt strip_tac >> CONV_TAC SYM_CONV >> first_x_assum irule >>
      fs [word_add_n2w,w2n_n2w,dimword_64,bootDataRam_def,
          initialPc_def,bootstrap_size] >> decide_tac) >>
  metis_tac [bootstrap_instruction_fetch]
QED
Theorem bootstrap_asm_step:
  MEM (pc,instruction) bootstrapBlocks /\ bootstrapRomInvariant input s /\
  s.pc = n2w pc /\ s.lr = 1 /\ ~s.be /\ s.align = 2 /\
  ~(bootAfter instruction s).failed ==>
  asm_step riscv_config s instruction (bootAfter instruction s)
Proof
  strip_tac >>
  `bytes_in_memory (n2w pc) (riscv_enc instruction) s.mem s.mem_domain` by
    metis_tac [bootstrap_fetch_from_frame] >>
  `asm_ok instruction riscv_config` by
    (mp_tac bootstrap_instructions_admitted >>
     rewrite_tac [EVERY_MEM] >>
     disch_then (qspec_then `(pc,instruction)` mp_tac) >> simp []) >>
  fs [asm_step_def,riscv_config_def,bootAfter_def] >>
  qpat_x_assum `~(asm _ _ _).failed` mp_tac >>
  asm_simp_tac std_ss [WORD_ADD_COMM]
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "bootstrap step assumptions")
  [bootstrap_instruction_bounds,bootstrap_fetch_from_frame,bootstrap_asm_step];
