(* Data-only OpenTheory replay. No candidate ML, no axiom_in_db fallback.
   This is a checked component, not yet a complete challenge verifier. *)
structure strictReplayLib =
struct
open HolKernel boolLib bossLib;

(* These are exactly HOL's fixed foundational axioms, not article requests. *)
val kernel_axioms = [boolTheory.BOOL_CASES_AX, boolTheory.ETA_AX,
                     boolTheory.SELECT_AX, boolTheory.INFINITY_AX];

fun reject s = raise Fail ("certificate replay: " ^ s);
fun checked th =
  if Tag.isEmpty (Thm.tag th) orelse Tag.isDisk (Thm.tag th) then th
  else reject "theorem uses an oracle or additional axiom";

fun same_sequent (hs,c) th =
  aconv c (concl th) andalso
  HOLset.equal (HOLset.addList (empty_tmset,hs), hypset th);

(* Fixed library facts may be requested with quantified variables instantiated
   or conjunctions projected. These steps are kernel inferences, too. *)
fun instance facts seq =
  let
    val (_,c) = seq;
    val (variables,body) = strip_forall c;
    fun attempt th =
      let val result = GENL variables (PART_MATCH I (checked th) body)
      in if same_sequent seq result then SOME (checked result) else NONE end
      handle HOL_ERR _ => NONE;
    fun first [] = NONE
      | first (th::rest) =
          case attempt th of SOME result => SOME result | NONE => first rest;
    fun search [] = NONE
      | search (th::rest) =
          case first (th :: CONJUNCTS (SPEC_ALL th)) of
            SOME result => SOME result | NONE => search rest;
  in search facts end;

(* Article-defined CV functions have no cv_trans metadata. Recover their code
   equations only from already checked theorems, then ask the kernel compute
   primitive to prove the requested equality. No article equation is assumed. *)
val cv_primitives =
  let open cvSyntax in
    [cv_pair_tm,cv_num_tm,cv_fst_tm,cv_snd_tm,cv_ispair_tm,
     cv_add_tm,cv_sub_tm,cv_mul_tm,cv_div_tm,cv_mod_tm,
     cv_lt_tm,cv_if_tm,cv_eq_tm]
  end;

fun code_expression tm =
  type_of tm = cvSyntax.cv andalso
  (if is_var tm then true
   else if cvSyntax.is_cv_num tm then
     numSyntax.is_numeral (cvSyntax.dest_cv_num tm)
   else if boolSyntax.is_let tm then
     let val (binding,value) = boolSyntax.dest_let tm
         val (v,body) = dest_abs binding
     in type_of v = cvSyntax.cv andalso code_expression value andalso
        code_expression body end
   else let val (f,args) = strip_comb tm
        in is_const f andalso not (null args) andalso
           List.all code_expression args end)
  handle HOL_ERR _ => false;

fun raw_compute facts c =
  let
    val (lhs,_) = dest_eq c;
    val _ = if code_expression lhs andalso null (free_vars lhs)
            then () else reject "not a closed executable CV computation";
    (* Representation theorems can have the same head as executable code.
       Select only equations in the kernel evaluator's CV expression language. *)
    fun equation th =
      let
        val th = SPEC_ALL (checked th);
        val (l,r) = dest_eq (concl th);
        val (f,args) = strip_comb l;
        val _ = if null (hyp th) andalso is_const f andalso not (null args)
                   andalso not (List.exists (aconv f) cv_primitives)
                   andalso code_expression r
                   andalso List.all (fn v => is_var v andalso type_of v = cvSyntax.cv) args
                   andalso HOLset.numItems (HOLset.addList (empty_tmset,args)) = length args
                   andalso List.all (fn v => List.exists (aconv v) args) (free_vars r)
                then () else raise Fail "not a code equation";
      in SOME (f,(th,r)) end
      handle HOL_ERR _ => NONE | Fail _ => NONE;
    (* Primitive-only arithmetic needs no scan of the accumulated code facts. *)
    fun from_equations () =
      let
        val equations = List.mapPartial equation
          (List.concat (map (CONJUNCTS o SPEC_ALL o checked) facts));
        fun collect [] seen result = result
          | collect (f::todo) seen result =
              if List.exists (aconv f) seen then collect todo seen result
              else case List.find (fn (g,_) => aconv f g) equations of
                NONE => collect todo (f::seen) result
              | SOME (_,(th,r)) => collect (find_terms is_const r @ todo)
                                          (f::seen) (th::result);
        val code = collect (find_terms is_const lhs) [] [];
      in cv_computeLib.cv_compute code lhs end;
  in cv_computeLib.cv_compute [] lhs
     handle HOL_ERR _ => from_equations () end;

(* Re-prove large byte-list decoding without an article containing one proof
   step per byte. A named RHS must resolve to an already checked definition. *)
fun decode_literal facts c =
  let
    val (l,r) = dest_eq c;
    val (f,value) = dest_comb l;
    val expected = ``cv_type$to_list (cv_type$to_word : cv -> word8)``;
    val _ = if aconv f expected then () else reject "not a byte decoding request";
    val decoded = literalDecodeLib.decode value;
    fun literal_definition th =
      null(hyp th) andalso is_eq (concl th) andalso
      aconv (lhs(concl th)) r andalso aconv (rhs(concl th)) (rhs(concl decoded));
  in if aconv (rhs(concl decoded)) r then decoded
     else case List.find literal_definition facts of
       SOME def => TRANS decoded (SYM (checked def))
     | NONE => reject "decoded bytes differ from the fixed literal"
  end;

(* EVAL requests are limited to the fixed vocabulary. Candidate definitions
   must supply their checked equations through the raw CV path above. *)
fun fixed_eval c =
  let
    val _ = if is_forall c orelse is_exists c orelse not (null (free_vars c))
            then reject "symbolic request requires a proved library fact" else ();
    val _ = if List.exists
      (fn tm => #Thy (dest_thy_const tm) = current_theory ())
      (find_terms is_const c) then reject "candidate constant in fixed EVAL request"
      else ();
  in EQT_ELIM ((bossLib.EVAL THENC
       QCONV (REWRITE_CONV [checked wordsTheory.word_0_n2w,
                           checked wordsTheory.word_1_n2w,
                           checked wordsTheory.ZERO_LT_dimword,
                           checked wordsTheory.ONE_LT_dimword])) c) end;

fun bool_taut c =
  let
    val (variables,body) = strip_forall c;
    fun propositional tm =
      if is_var tm then type_of tm = bool
      else if aconv tm T orelse aconv tm F then true
      else let val (f,args) = strip_comb tm
               val {Thy,Name,...} = dest_thy_const f
           in ((Thy = "min" andalso (Name = "=" orelse Name = "==>")) orelse
               (Thy = "bool" andalso
                List.exists (fn n => n = Name) ["/\\","\\/","~"])) andalso
              List.all propositional args end
           handle HOL_ERR _ => false;
    val _ = if propositional body then () else reject "not a propositional request";
  in GENL variables (tautLib.TAUT_PROVE body) end;

(* Keep this early simplifier away from large computation literals. *)
fun bounded_term limit tm =
  let
    exception TooLarge;
    fun visit 0 _ = raise TooLarge
      | visit n t =
          if is_comb t then let val (f,x) = dest_comb t
                            in visit (visit (n-1) f) x end
          else if is_abs t then visit (n-1) (snd(dest_abs t))
          else n-1;
  in (ignore(visit limit tm); true) handle TooLarge => false end;

fun small_logical tm = bounded_term 256 tm;

(* Use only checked datatype equations for the types occurring in a small
   request, including constructor distinctness and injectivity. *)
fun datatype_rewrites c =
  if small_logical c then
    let
      val types = Lib.mk_set (map type_of (find_terms (K true) c));
      fun rewrites ty = map checked (#rewrs (TypeBase.simpls_of ty))
                        handle HOL_ERR _ => [];
    in List.concat (map rewrites types) end
  else [];

fun logical_simp c =
  EQT_ELIM (QCONV (SIMP_CONV bool_ss
    (datatype_rewrites c @
     [boolTheory.FUN_EQ_THM, boolTheory.RIGHT_FORALL_OR_THM,
      boolTheory.LEFT_FORALL_OR_THM, boolTheory.FORALL_AND_THM,
      pairTheory.PAIR, combinTheory.I_THM, numeralTheory.numeral_evenodd])) c)
  handle original as HOL_ERR _ =>
    if small_logical c then
      (numLib.ARITH_PROVE c handle HOL_ERR _ => raise original)
    else raise original;

fun logical_compute c =
  logical_simp c
  handle HOL_ERR _ =>
    (bool_taut c handle HOL_ERR _ =>
      (fixed_eval c handle HOL_ERR _ => EQT_ELIM (cv_transLib.cv_eval c))
      | Fail _ => (fixed_eval c handle HOL_ERR _ => EQT_ELIM (cv_transLib.cv_eval c)));

(* Computation requests are re-proved by the local HOL kernel. An article
   cannot make the result trusted merely by labelling it an axiom. *)
fun resolve_fallback trusted proved (hs,c) =
  let
    val facts = trusted @ Net.listItems proved;
    val primitive = if null hs then
      let val th = raw_compute [] c
      in if same_sequent (hs,c) th then SOME (checked th) else NONE end
      handle HOL_ERR _ => NONE | Fail _ => NONE
      else NONE;
  in case primitive of
    SOME th => th
  | NONE => case List.find (same_sequent (hs,c)) facts of
    SOME th => checked th
  | NONE =>
      if not (null hs) then reject "unresolved assumption"
      else let
        val th = case instance facts (hs,c) of
          SOME th => th
        | NONE => (decode_literal facts c
                   handle HOL_ERR _ => raw_compute facts c
                        | Fail _ => raw_compute facts c)
                 handle e as HOL_ERR _ =>
                   if is_eq c andalso code_expression (lhs c)
                   then raise e else logical_compute c
                      | e as Fail _ =>
                   if is_eq c andalso code_expression (lhs c)
                   then raise e else logical_compute c
      in if same_sequent (hs,c) th then checked th
         else reject "computation proved a different statement" end
  end
  handle cv_repLib.NeedsTranslation _ => reject "no checked computation for requested theorem";

(* Most requests name a theorem already present verbatim. Index that path
   once for the fixed library and use the reader's existing theorem net for
   article facts, retaining exact sequent and tag checks after lookup. *)
(* Huge literal facts remain in the complete fallback library, but are kept
   out of structural fast indexes to bound index construction memory. *)
fun resolve trusted =
  let
    val index = List.foldl (fn (th,net) => Net.insert(concl th,th) net) Net.empty
      (List.filter (bounded_term 4096 o concl) trusted);
    fun variants th = th :: CONJUNCTS (SPEC_ALL (checked th));
    val patterns = List.foldl
      (fn (th,net) => Net.insert(snd(strip_forall(concl th)),th) net)
      Net.empty (List.filter (bounded_term 4096 o concl)
        (List.concat(map variants trusted)));
    fun lookup proved (seq as (hs,c)) =
      case List.find (same_sequent seq) (Net.index c index @ Net.index c proved) of
        SOME th => SOME (checked th)
      | NONE => instance (Net.match (snd(strip_forall c)) patterns) seq;
    (* Writer requests sometimes wrap a proved proposition in equality with T.
       Normalize only small requests, then transport the matched checked fact
       back through the kernel conversion to the exact original sequent. *)
    fun normalized_lookup proved (seq as (hs,c)) =
      if not (small_logical c) then NONE else
      let val conversion = QCONV (SIMP_CONV bool_ss []) c;
          val normalized = rhs (concl conversion);
      in if aconv c normalized then NONE else
           case lookup proved (hs,normalized) of
             NONE => NONE
           | SOME th =>
               let val result = checked (EQ_MP (SYM conversion) (checked th))
               in if same_sequent seq result then SOME result else NONE end
      end handle HOL_ERR _ => NONE | Fail _ => NONE;
  in fn proved => fn seq as (hs,c) =>
    case lookup proved seq of
      SOME th => checked th
    | NONE =>
      (case normalized_lookup proved seq of
         SOME th => checked th
       | NONE =>
           let val simple = if null hs andalso small_logical c then
                 SOME (logical_simp c handle HOL_ERR _ => bool_taut c)
                 handle HOL_ERR _ => NONE | Fail _ => NONE
               else NONE
           in case simple of
                SOME th => if same_sequent seq th then checked th
                           else resolve_fallback trusted proved seq
              | NONE => resolve_fallback trusted proved seq
           end)
  end;

(* Logical names may contain punctuation. Only the ML theorem binding needs
   an identifier; hexadecimal byte encoding is injective and leaves the logical
   constant name unchanged. *)
fun definition_binding name = "article_" ^ String.concat
  (map (fn c => StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c)))
       (String.explode name));

(* Candidate definitions may only extend a fresh, operator-created theory.
   Fixed challenge, library, bytecode and score constants cannot be replaced. *)
fun reader trusted =
  let
    val namespace = current_theory ();
    fun const_name (["HOL4",thy],name) = {Thy=thy,Name=name}
      | const_name n = OpenTheoryReader.const_name_in_map n;
    fun tyop_name (["HOL4",thy],name) = {Thy=thy,Tyop=name}
      | tyop_name n = OpenTheoryReader.tyop_name_in_map n;
    fun def_const (c as {Thy,...}) rhs =
      if Thy = namespace andalso not (can prim_mk_const c)
      then OpenTheoryReader.define_const_in_thy definition_binding c rhs
      else reject "definition outside candidate theory";
    fun def_type (r as {name={Thy,...},rep,abs,...}) =
      if Thy = namespace andalso #Thy rep = namespace andalso #Thy abs = namespace
         andalso not (Option.isSome (Type.op_arity (#name r)))
         andalso not (can prim_mk_const rep) andalso not (can prim_mk_const abs)
      then OpenTheoryReader.define_tyop_in_thy r
      else reject "type definition outside candidate theory";
  in {const_name=const_name, tyop_name=tyop_name,
      define_const=def_const, define_tyop=def_type,
      axiom=resolve (map checked trusted)} end;

fun read trusted expected input =
  let
    val _ = if type_of expected = bool andalso null (free_vars expected)
            then () else reject "expected statement is not closed";
    val proved = articleReaderLib.raw_read_article input (reader trusted);
  in case List.find (same_sequent ([],expected)) (Net.listItems proved) of
       NONE => reject "exact fixed certificate conclusion was not proved"
     | SOME th => checked th
  end;
end
