(* Normalize record literals to constructors by proved reconstruction equations.
   This removes the syntactic ARB base of fully specified record literals. *)
structure recordLiteralLib =
struct
open HolKernel boolLib bossLib;
val cache = ref ([] : (hol_type * thm) list);
fun reconstruction ty =
  case List.find (fn (t,_) => t = ty) (!cache) of SOME(_,th) => th | NONE =>
  let
    val equations = map (dest_eq o concl o SPEC_ALL) (TypeBase.accessors_of ty);
    val (constructor,args) = strip_comb (rand (#1 (hd equations)));
    fun accessor position =
      let fun matches (left,right) =
            aconv (List.nth (#2 (strip_comb (rand left)),position)) right
      in rator (#1 (valOf (List.find matches equations))) end;
    val r = mk_var ("record_value",ty);
    val value = list_mk_comb (constructor,
      List.tabulate (length args,fn i => mk_comb (accessor i,r)));
    val theorem = prove (mk_eq (r,value), Cases_on `record_value` >> simp []);
    val _ = cache := (ty,theorem) :: !cache;
  in theorem end;
fun literal tm =
  if TypeBase.is_record tm andalso not (null (#2 (TypeBase.dest_record tm)))
     andalso not (TypeBase.is_constructor (fst (strip_comb tm))) then
    (REWR_CONV (reconstruction (type_of tm)) THENC EVAL) tm
  else NO_CONV tm;
val normalize = EVAL THENC TOP_DEPTH_CONV literal THENC EVAL THENC
  REWRITE_CONV [cvTheory.b2c_def] THENC EVAL;
end
