(* Smoke-check the proof-producing restricted symbolic evaluator. *)
Theory initRestrictedEvaluator
Ancestors initRestrictedRules
Libs preamble riscv_stepLib restrictedStepLoaderLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = restrictedStepLoaderLib.load ();
val _ = List.app (fn (name,opcode) =>
  let val th = restrictedStepLoaderLib.riscv_step_hex opcode |> DISCH_ALL
  in if null(hyp th) then ignore(save_thm(name,check_thm th))
     else failwith "restricted evaluator assumptions" end)
  [("restricted_addi_step","00828293"),
   ("restricted_load_step","0002be03"),
   ("restricted_store_step","01c33023"),
   ("restricted_branch_step","fe7368e3"),
   ("restricted_jump_step","3340006f")];
val rejected =
  ((ignore(restrictedStepLoaderLib.riscv_step_hex "0000003b"); false)
   handle HOL_ERR _ => true);
val _ = if rejected then () else failwith "unsupported ADDW was accepted";
