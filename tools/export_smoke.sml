(* Author-side export regression; run through tools/test_exporter.py. *)
val _ = TraceMode.mode := TraceMode.TraceOnly;
load "cv_computeLib";
load "Logging";
open HolKernel boolLib bossLib;
val _ = PolyML.print_depth 0;
val _ = new_theory "exportSmoke";
val _ = TraceMode.mode := TraceMode.TraceOnly;
val _ = Logging.set_const_name_handler
  (fn {Thy,Name} => (["HOL4",if Thy = "exportSmoke" then "candidateCertificate" else Thy],Name));
val _ = Logging.set_tyop_name_handler
  (fn {Thy,Tyop} => (["HOL4",Thy],Tyop));
val _ = Logging.raw_start_logging [] (TextIO.openOut "cv-smoke.art");
val _ = Logging.export_thm boolTheory.SELECT_AX;
val dotted = new_definition ("dotted_binding",
  mk_eq(mk_var("helper.with.dots",``:cv``),``cv$Num 19``));
val _ = Logging.export_thm dotted;
val specs = gen_new_specification("smoke_pair",
 CONJ (ASSUME ``leftValue = cv$Num 2``) (ASSUME ``rightValue = cv$Num 5``));
val _ = Logging.export_thm specs;
val code = new_definition("smoke_def",``smoke x = cv$cv_add x (cv$Num 7)``);
val result = cv_computeLib.cv_compute [code] ``smoke (cv$Num 10)``;
val _ = Logging.export_thm result;
val _ = Logging.flush_dictionary ();
val _ = List.app (fn _ => ignore (Logging.export_thm result)) (List.tabulate (33,I));
val decoded = literalDecodeLib.decode
  ``cv$Pair (cv$Num 0) (cv$Pair (cv$Num 255) (cv$Pair (cv$Num 17) (cv$Num 0)))``;
val _ = if aconv (rhs (concl decoded)) ``[0w;255w;17w] : word8 list`` then ()
        else raise Fail "literal decoder mismatch";
val _ = Logging.export_thm decoded;
val byte_literal = new_definition ("smokeBytes_def",
  mk_eq (mk_var ("smokeBytes",``:word8 list``),rhs(concl decoded)));
val _ = Logging.export_thm byte_literal;
val request = TRANS decoded (SYM byte_literal);
val _ = Thm.delete_proof request;
val _ = Logging.export_thm request;
val evaluated = Lib.with_flag (TraceMode.mode,TraceMode.NoTrace)
  EVAL ``LENGTH [T;F;T] = 3``;
val _ = Logging.export_thm evaluated;
fun export_solved tactic goal context =
  let val (goals,validate) = tactic goal context
  in if null goals then
    let val th = validate []
        val _ = Logging.export_thm th
        val _ = Logging.flush_dictionary ()
    in ([],fn _ => th) end
  else (goals,validate) end;
val eager_result = prove (``(p:bool) ==> p``,
  DISCH_TAC >> export_solved (ASM_REWRITE_TAC []));
val _ = Logging.export_thm eager_result;
val _ = Logging.stop_logging ();
val _ = print "EXPORT_SMOKE_OK\n";
