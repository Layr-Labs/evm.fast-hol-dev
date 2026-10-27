(* The exact compiler pipeline has no dynamic-install instruction at lab level. *)
Theory initNoInstall
Ancestors initCorrectnessInput initSourceChecks
Libs preamble
open backendTheory pan_to_targetProofTheory initCompilationInputTheory
  initSourceChecksTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition guestLabProgram_def:
  guestLabProgram =
    let c = set_oracle guestConfig allocation in
    let (col,wprog) = word_to_word$compile c.word_to_word_conf riscv_config prepared_word in
    let (bm,wc,fs,p) = word_to_stack$compile riscv_config F wprog in
      stack_to_lab$compile (arch_wordsize riscv_config.ISA)
        c.stack_conf c.data_conf
        (&(2 * data_to_word$max_heap_limit 64 c.data_conf - 1))
        (riscv_config.reg_count - (LENGTH riscv_config.avoid_regs + 3))
        riscv_config.addr_offset p
End
Theorem guest_lab_no_install:
  labProps$no_install guestLabProgram
Proof
  simp [guestLabProgram_def,LET_DEF] >>
  rpt (pairarg_tac >> fs []) >>
  irule (INST_TYPE [alpha |-> ``:64``] from_pan_to_lab_no_install) >>
  simp [riscv_isa] >>
  metis_tac [guest_to_word,prepared_distinct_functions]
QED
val _ = if null(hyp guest_lab_no_install)
  then ignore(check_thm guest_lab_no_install)
  else failwith "no-install compilation assumptions";
