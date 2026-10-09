(* Adapted from HOL4 OpenTheoryReader.sml at the tested HOL pin.
   See HOL-LICENSE. Adds the writer's version-6 sym/trans/hdTl/defineConstList
   commands. Every proof operation uses HOL kernel rules; all axiom and
   definition requests go through the caller's strict callbacks. *)
structure articleReaderLib =
struct
open HolKernel Drule boolSyntax OpenTheoryMap OpenTheoryCommon;
val ERR = mk_HOL_ERR "articleReaderLib";
val NUMERAL_conv = OpenTheoryReader.NUMERAL_conv;
fun DEDUCT_ANTISYM th1 th2 =
  IMP_ANTISYM_RULE (DISCH (concl th2) th1) (DISCH (concl th1) th2);
fun st_(st,{stack,dict,thms,line_num}) = {stack=st,dict=dict,thms=thms}
fun push (ob,st) = st_(ob::(#stack st),st)
local open Substring in
  val trimlr = fn s => string(trimr 1 (triml 1 (full s)))
  val trimr  = fn s => string(trimr 1 (full s))
end

fun raw_read_article input
  {const_name,tyop_name,define_tyop,define_const,axiom} = let
  val ERR = ERR "read_article"
  fun unOTermls c = List.map (fn OTerm t => t | _ => raise ERR (c^" failed to pop a list of terms"))
  fun unOTypels c = List.map (fn OType t => t | _ => raise ERR (c^" failed to pop a list of types"))
  fun ot_to_const c s = const_name (string_to_otname s)
  handle _ => raise ERR (c^": no map from "^s^" to a constant")
  fun ot_to_tyop  c s = tyop_name (string_to_otname s)
  handle _ => raise ERR (c^": no map from "^s^" to a type operator")
  val mk_vartype = mk_vartype o tyvar_from_ot o string_to_otname
  fun f "absTerm"(st as {stack=OTerm b::OVar v::os,...}) = st_(OTerm(mk_abs(v,b))::os,st)
    | f "absThm" (st as {stack=OThm th::OVar v::os,...}) = (st_(OThm(ABS v th)::os,st)
      handle HOL_ERR e => raise ERR "absThm: failed")
    | f "appTerm"(st as {stack=OTerm x::OTerm f::os,...})= st_(OTerm(mk_comb(f,x))::os,st)
    | f "appThm" (st as {stack=OThm xy::OThm fg::os,...})= let
        val (f,g) = dest_eq(concl fg)
        val (x,y) = dest_eq(concl xy)
        val fxgx  = AP_THM fg x
        val gxgy  = AP_TERM g xy
      in st_(OThm(TRANS fxgx gxgy)::os,st) end
    | f "sym" (st as {stack=OThm th::os,...}) = st_(OThm(SYM th)::os,st)
    | f "trans" (st as {stack=OThm t2::OThm t1::os,...}) = st_(OThm(TRANS t1 t2)::os,st)
    | f "hdTl" (st as {stack=OList(h::t)::os,...}) = st_(OList t::h::os,st)
    | f "assume"       (st as {stack=OTerm t::os,...})          = st_(OThm(ASSUME t)::os,st)
    | f "axiom"        (st as {stack=OTerm t::OList ts::os,thms,...}) = st_(OThm(axiom thms (unOTermls "axiom" ts,t))::os,st)
    | f "betaConv"     (st as {stack=OTerm t::os,...})          = st_(OThm(BETA_CONV t)::os,st)
    | f "cons"         (st as {stack=OList t::h::os,...})       = st_(OList(h::t)::os,st)
    | f "const"        (st as {stack=OName n::os,...})          = st_(OConst (ot_to_const "const" n)::os,st)
    | f "constTerm"    (st as {stack=OType Ty::OConst {Thy,Name}::os,...})
                     = st_(OTerm(mk_thy_const {Ty=Ty,Thy=Thy,Name=Name})::os,st)
    | f "deductAntisym"(st as {stack=OThm t1::OThm t2::os,...}) = st_(OThm(DEDUCT_ANTISYM t1 t2)::os,st)
    | f "def"         {stack=ONum k::x::os,dict,thms,...}       = {stack=x::os,dict=Map.insert(dict,k,x),thms=thms}
    | f "defineConst" (st as {stack=OTerm t::OName n::os,...})  = let
        val c = ot_to_const "defineConst" n
        val def = define_const c t
        handle Map.NotFound => raise ERR ("defineConst: no map from "^thy_const_to_string c^" to a definition function")
      in st_(OThm def::OConst c::os,st) end
    | f "defineConstList" (st as {stack=OThm th::OList entries::os,...}) = let
        fun entry (OList[OName name,OVar v]) = (ot_to_const "defineConstList" name,v)
          | entry _ = raise ERR "defineConstList: expected name-variable pairs"
        val entries = map entry entries
        fun definition (name,v) = let
          val premise = Lib.first (fn h => is_eq h andalso aconv (lhs h) v) (hyp th)
          val def = define_const name (rhs premise)
        in (v,lhs(concl def),def) end
        val definitions = map definition entries
        val substitution = map (fn (v,c,_) => v |-> c) definitions
        val result = INST substitution th
        val result = List.foldl (fn ((_,_,def),th) => PROVE_HYP def th) result definitions
        val constants = map (fn (name,_) => OConst name) entries
      in st_(OThm result::OList constants::os,st) end
    | f "defineTypeOp"  (st as {stack=OThm ax::OList ls::OName rep::OName abs::OName n::os,...}) = let
        val ls = List.map (fn OName s => mk_vartype s | _ => raise ERR "defineTypeOp failed to pop a list of names") ls
        val tyop = ot_to_tyop "defineTypeOp" n
        val ot_to_const = ot_to_const "defineTypeOp"
        val {abs_rep,rep_abs} = define_tyop {name=tyop,ax=ax,args=ls,rep=ot_to_const rep,abs=ot_to_const abs}
        val (abs,foo) = dest_comb(#2(dest_abs(lhs(concl abs_rep))))
        val (rep,_)   = dest_comb foo
        val {Thy,Name,...} = dest_thy_const rep val rep = {Thy=Thy,Name=Name}
        val {Thy,Name,...} = dest_thy_const abs val abs = {Thy=Thy,Name=Name}
      in st_(OThm rep_abs::OThm abs_rep::OConst rep::OConst abs::OTypeOp tyop::os,st) end
    | f "eqMp"   (st as {stack=OThm f::OThm fg::os,...})     = (st_(OThm(EQ_MP fg f)::os,st)
      handle HOL_ERR e => raise ERR "EqMp failed")
    | f "nil"    st                                          = push(OList [],st)
    | f "opType" (st as {stack=OList ls::OTypeOp {Thy,Tyop}::os,...})
               = st_(OType(mk_thy_type{Thy=Thy,Tyop=Tyop,Args=unOTypels "opType" ls})::os,st)

    | f "pop"    (st as {stack=x::os,...})                   = st_(os,st)
    | f "ref"    (st as {stack=ONum k::os,dict,...})         = st_(Map.find(dict,k)::os,st)
    | f "refl"   (st as {stack=OTerm t::os,...})             = st_(OThm(REFL t)::os,st)
    | f "remove" {stack=ONum k::os,dict,thms,...}            = let
        val (dict,x) = Map.remove(dict,k)
      in {stack=x::os,dict=dict,thms=thms} end
    | f "subst"  (st as {stack=OThm th::OList[OList tys,OList tms]::os,...}) = let
        val tys = List.map (fn OList [OName a, OType t] => {redex=mk_vartype a, residue=t}
                             | _ => raise ERR "subst failed to pop a list of [name,type] pairs") tys
        val tms = List.map (fn OList [OVar v, OTerm t] => {redex=v, residue=t}
                             | _ => raise ERR "subst failed to pop a list of [var,term] pairs") tms
        val th = INST_TYPE tys th
        val th = INST tms th
      in st_(OThm th::os,st) end
    | f "thm"    {stack=OTerm c::OList ls::OThm th::os,dict,thms,...} = let
        val th = EQ_MP (ALPHA (concl th) c) th
        handle HOL_ERR _ => raise ERR "thm: desired conclusion not alpha-equivalent to theorem's conclusion"
        fun ft (OTerm h, th) = let
          val c = concl th
          val th = DISCH h th
          val c' = concl th
        in
          if aconv c c' then
            Drule.ADD_ASSUM h th
          else let
            val (h',_) = boolSyntax.dest_imp c'
            val h'h = ALPHA h' h
            val th = Drule.SUBS_OCCS [([1],h'h)] th
          in Drule.UNDISCH th end
        end | ft _ = raise ERR "thm failed to pop a list of terms"
        val th = List.foldl ft th ls
      in {stack=os,dict=dict,thms=Net.insert(concl th,th)thms} end
    | f "typeOp"  (st as {stack=OName n::os,...})          = st_(OTypeOp (ot_to_tyop "typeOp" n)::os,st)
    | f "version" (st as {stack=ONum n::os,...})           = if n = 6 then st_(os,st) else raise ERR "unsupported article version"
    | f "var"     (st as {stack=OType t::OName n::os,...}) = st_(OVar(mk_var(n,t))::os,st)
    | f "varTerm" (st as {stack=OVar t::os,...})           = st_(OTerm t::os,st)
    | f "varType" (st as {stack=OName n::os,...})          = st_(OType(mk_vartype n)::os,st)
    | f s (st as {stack,dict,thms,line_num,...}) = let val c = String.sub(s,0) open Char Option Int
      in if c = #"\"" then push(OName(trimlr s),st) else
         if isDigit c then push(ONum(valOf(fromString s)),st) else
         if c = #"#" then {stack=stack,dict=dict,thms=thms} else
         raise ERR ("Unknown command (or bad arguments) on line "^(Int.toString line_num)^": <<"^s^">>")
      end
  fun loop (x as {line_num,...}) = case TextIO.inputLine input of
    NONE => x before TextIO.closeIn(input)
  | SOME line => let
      val {stack,dict,thms} = f (trimr line) x
        handle HOL_ERR error => raise ERR
          ("line " ^ Int.toString line_num ^ ": " ^
           Feedback.top_structure_of error ^ "." ^ Feedback.top_function_of error ^
           ": " ^ Feedback.message_of error)
             | Fail message => raise ERR
                 ("line " ^ Int.toString line_num ^ ": " ^ message)
    in loop {stack=stack,dict=dict,thms=thms,line_num=line_num+1} end
in
  Net.map (Conv.CONV_RULE NUMERAL_conv)
    (#thms (loop {stack=[],dict=Map.mkDict(Int.compare),thms=Net.empty,line_num=1}))
end

fun read_article s r = raw_read_article (TextIO.openIn s) r

end
