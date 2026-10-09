(* Kernel-checked literal helper: decode CV byte lists with shared proofs for the 256 bytes.
   Every output equality is built with kernel inference rules. *)
structure literalDecodeLib =
struct
open HolKernel boolLib bossLib;
fun decode value =
  let
val byte_step = prove
  (``!n tail. cv_type$to_list (cv_type$to_word : cv -> word8)
       (cv$Pair (cv$Num n) tail) =
       (n2w n : word8) :: cv_type$to_list cv_type$to_word tail``,
   simp [cv_typeTheory.to_list_def,cv_typeTheory.to_word_def,cvTheory.c2n_def]);
val empty = prove
  (``cv_type$to_list (cv_type$to_word : cv -> word8) (cv$Num 0) = []``,
   simp [cv_typeTheory.to_list_def]);
val steps = Vector.tabulate (256,fn n => SPEC (numSyntax.term_of_int n) byte_step);
val conses = Vector.tabulate (256,fn n =>
  rator (listSyntax.mk_cons (wordsSyntax.mk_wordii(n,8),listSyntax.mk_nil ``:word8``)));
    fun gather tm entries =
      if cvSyntax.is_cv_pair tm then
        let val (head,tail) = cvSyntax.dest_cv_pair tm
            val byte = numSyntax.int_of_term (cvSyntax.dest_cv_num head)
            val _ = if 0 <= byte andalso byte < 256 then ()
                    else raise Fail "CV byte is out of range"
        in gather tail ((byte,tail)::entries) end
      else if aconv tm (cvSyntax.mk_cv_num numSyntax.zero_tm) then entries
      else raise Fail "malformed CV byte-list terminator";
    fun step ((byte,tail),th) =
      TRANS (SPEC tail (Vector.sub(steps,byte)))
            (AP_TERM (Vector.sub(conses,byte)) th);
  in List.foldl step empty (gather value []) end;
end
