(* Derive a local evaluator from the pinned HOL source. Every decoded
   constructor must have a kernel proof of support before the restricted
   step rule can be applied. The upstream checkout is never edited. *)
structure restrictedStepLoaderLib :> restrictedStepLoaderLib = struct
open HolKernel;
val evaluator : (Term.term -> Thm.thm) ref = ref (fn _ => raise Fail "restricted evaluator not loaded");
val hex_evaluator : (string -> Thm.thm) ref = ref (fn _ => raise Fail "restricted evaluator not loaded");
fun register (step,hex_step) = (evaluator := step; hex_evaluator := hex_step);
fun riscv_step tm = (!evaluator) tm;
fun riscv_step_hex text = (!hex_evaluator) text;
fun read path =
  let val stream = TextIO.openIn path
      val source = TextIO.inputAll stream
      val _ = TextIO.closeIn stream
  in source end;
fun replace_once old replacement source =
  let val n = size old
      fun find i =
        if i+n > size source then raise Fail "pinned RISC-V evaluator has changed"
        else if String.substring(source,i,n) = old then i else find (i+1)
      val i = find 0
      val rest = String.extract(source,i+n,NONE)
      val _ = if String.isSubstring old rest then
                raise Fail "ambiguous RISC-V evaluator patch" else ()
  in String.substring(source,0,i) ^ replacement ^ rest end;
fun load () =
  let val path = OS.Path.concat (Globals.HOLDIR,
        "examples/l3-machine-code/riscv/step/riscv_stepLib.sml")
      val source = read path
        |> replace_once "structure riscv_stepLib :> riscv_stepLib ="
             "structure restrictedRiscvStepLib :> riscv_stepLib ="
        |> replace_once "val MP_Next_n = next riscv_stepTheory.NextRISCV"
             "val MP_Next_n = next initRestrictedRulesTheory.restricted_next_normal"
        |> replace_once "val MP_Next_c = next riscv_stepTheory.NextRISCV_cond_branch"
             "val MP_Next_c = next initRestrictedRulesTheory.restricted_next_cond_branch"
        |> replace_once "val MP_Next_b = next riscv_stepTheory.NextRISCV_branch"
             "val MP_Next_b = next initRestrictedRulesTheory.restricted_next_branch"
        |> replace_once "val thm2 = riscv_decode v |> SIMP_RULE std_ss []"
             ("val decoded = riscv_decode v |> SIMP_RULE std_ss []\n" ^
             "      val support = mk_comb(prim_mk_const {Thy=\"initTarget\", Name=\"supported_instruction\"}, rhs(concl decoded))\n" ^
             "        |> SIMP_CONV (srw_ss()) [initTargetTheory.supported_instruction_def] |> EQT_ELIM\n" ^
             "      val thm2 = MATCH_MP initRestrictedRulesTheory.restricted_decoded_word (CONJ decoded support)")
      val generated = "restrictedRiscvStepGenerated.sml"
      val output = TextIO.openOut generated
      val _ = TextIO.output(output,source ^ "\nval _ = restrictedStepLoaderLib.register (restrictedRiscvStepLib.riscv_step, restrictedRiscvStepLib.riscv_step_hex);\n")
      val _ = TextIO.closeOut output
  in Meta.qquse generated end;
end
