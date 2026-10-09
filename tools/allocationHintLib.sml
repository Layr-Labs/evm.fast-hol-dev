(* Author-only data encoding. No theorem is read or trusted through this file. *)
structure allocationHintLib =
struct
open HolKernel;
fun write path value =
  let
    val stream = TextIO.openOut path;
    fun line s = TextIO.output(stream,s ^ "\n");
    fun number tm = line (Arbnum.toString (numSyntax.dest_numeral tm));
    fun tree tm =
      if sptreeSyntax.is_ln tm then line "Ln"
      else if sptreeSyntax.is_ls tm then (line "Ls"; number (sptreeSyntax.dest_ls tm))
      else if sptreeSyntax.is_bn tm then
        let val (l,r) = sptreeSyntax.dest_bn tm in line "Bn"; tree l; tree r end
      else let val (l,n,r) = sptreeSyntax.dest_bs tm
           in line "Bs"; tree l; number n; tree r end;
    fun entry tm = if optionSyntax.is_none tm then line "N"
                   else (line "S"; tree (optionSyntax.dest_some tm));
    val _ = List.app entry (#1 (listSyntax.dest_list value));
    val _ = line "E";
  in TextIO.closeOut stream end;
fun read path =
  let
    val stream = TextIO.openIn path;
    fun next () = case TextIO.inputLine stream of
      NONE => raise Fail "truncated allocation hint"
    | SOME s => String.substring(s,0,size s - 1);
    fun number () = numSyntax.mk_numeral (Arbnum.fromString (next ()));
    fun tree () = case next () of
      "Ln" => sptreeSyntax.mk_ln numSyntax.num
    | "Ls" => sptreeSyntax.mk_ls (number ())
    | "Bn" => let val l = tree () val r = tree () in sptreeSyntax.mk_bn(l,r) end
    | "Bs" => let val l = tree () val n = number () val r = tree ()
              in sptreeSyntax.mk_bs(l,n,r) end
    | _ => raise Fail "invalid allocation tree";
    val ty = sptreeSyntax.mk_sptree_ty numSyntax.num;
    fun entries acc = case next () of
      "E" => List.rev acc
    | "N" => entries (optionSyntax.mk_none ty :: acc)
    | "S" => let val entry = optionSyntax.mk_some (tree ()) in entries (entry::acc) end
    | _ => raise Fail "invalid allocation entry";
    val result = listSyntax.mk_list(entries [],optionSyntax.mk_option ty);
    val _ = if TextIO.endOfStream stream then () else raise Fail "trailing allocation data";
  in TextIO.closeIn stream; result end;
end
