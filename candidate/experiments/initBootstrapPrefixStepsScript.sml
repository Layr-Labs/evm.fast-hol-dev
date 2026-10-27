(* The startup prefix executes through the actual assembler-step relation. *)
Theory initBootstrapPrefixSteps
Ancestors initBootstrapStep initBootstrapStartup
Libs preamble wordsLib cv_transLib
open asmSemTheory wordsTheory initBootstrapTheory initBootstrapLoopTheory
  initParamsTheory;
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
Definition bootSteps_def:
  bootSteps [] (s:64 asm_state) = T /\
  bootSteps (instruction::rest) s =
    (asm_step riscv_config s instruction (bootAfter instruction s) /\
     bootSteps rest (bootAfter instruction s))
End
val instructions = fst (listSyntax.dest_list (rhs (concl bootstrap_prefix)));
val enc_lengths = map (fn instruction => cv_eval ``LENGTH (riscv_enc ^instruction)``) instructions;
val membership = map (fn (pc,instruction) => EVAL
  ``MEM (^pc,^instruction) bootstrapBlocks``)
  (ListPair.zip (map numSyntax.term_of_int [2147483648,2147483656,2147483664],instructions));
Theorem bootstrap_prefix_steps:
  bootstrapRomInvariant input s /\ s.pc = n2w initialPc /\
  s.lr = 1 /\ ~s.be /\ s.align = 2 /\ ~s.failed ==>
  bootSteps bootstrapPrefix s
Proof
  strip_tac >> simp [bootstrap_prefix,bootSteps_def] >> rpt conj_tac
  >- (irule (Q.INST [`pc` |-> `0x80000000`, `input` |-> `input`] bootstrap_asm_step) >>
      fs (membership @ enc_lengths @ [bootAfter_def,asm_def,upd_pc_def,upd_reg_def,
        initialPc_def]) >> metis_tac [])
  >- (irule (Q.INST [`pc` |-> `0x80000008`, `input` |-> `input`] bootstrap_asm_step) >>
      fs (membership @ enc_lengths @ [bootAfter_def,asm_def,upd_pc_def,upd_reg_def,
        bootstrapRomInvariant_def,initialPc_def]) >> metis_tac []) >>
  irule (Q.INST [`pc` |-> `0x80000010`, `input` |-> `input`] bootstrap_asm_step) >>
  fs (membership @ enc_lengths @ [bootAfter_def,asm_def,upd_pc_def,upd_reg_def,
    bootstrapRomInvariant_def,initialPc_def,WORD_ADD_ASSOC]) >> metis_tac []
QED
val _ = List.app (fn th => if null (hyp th) then ignore (check_thm th)
  else failwith "bootstrap prefix steps assumptions")
  (bootstrap_prefix_steps :: enc_lengths @ membership);
