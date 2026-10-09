(* Byte and word domains of the fixed bitmap allocation. *)
Theory initBitmapDomain
Ancestors initBootstrap alignment
Libs preamble wordsLib
open wordsTheory alignmentTheory initBootstrapTheory;
Definition bitmapDomain_def:
  bitmapDomain = {a:word64 | bootDataRam+24 <= w2n a /\ w2n a < bootDataEnd}
End
Theorem bitmap_word_domain:
  byte_aligned INTER bitmapDomain =
  IMAGE (\i. n2w (bootDataRam+24+8*i):word64) (count 4614)
Proof
  simp [EXTENSION,bitmapDomain_def,IN_DEF,byte_aligned_def,aligned_w2n,
    dimindex_64,bootDataRam_def,bootDataEnd_def] >>
  gen_tac >> eq_tac
  >- (strip_tac >>
      qexists_tac `w2n x DIV 8 - 335560707` >>
      mp_tac (Q.SPEC `w2n (x:word64)` (MATCH_MP DIVISION (DECIDE ``0 < 8:num``))) >>
      strip_tac >>
      `w2n x = 8 * (w2n x DIV 8 - 335560707) + 2684485656` by decide_tac >>
      conj_tac >- metis_tac [n2w_w2n] >> decide_tac) >>
  strip_tac >> gvs [w2n_n2w,dimword_64] >> decide_tac
QED
Theorem aligned_interval_closed:
  byte_aligned (hi:'a word) /\
  w2n (lo:'a word) <= w2n (byte_align (a:'a word)) /\ w2n (byte_align a) < w2n hi ==>
  w2n lo <= w2n a /\ w2n a < w2n hi
Proof
  strip_tac >> conj_tac
  >- (mp_tac (Q.INST [`p` |-> `LOG2 (dimindex (:'a) DIV 8)`,`n` |-> `a:'a word`] align_ls) >>
      fs [WORD_LS,byte_align_def] >> decide_tac) >>
  Cases_on `byte_aligned a`
  >- fs [byte_align_aligned] >>
  metis_tac [aligned_between,byte_aligned_def,byte_align_def,WORD_LO]
QED
Theorem bitmap_domain_align_closed:
  byte_align a IN bitmapDomain ==> a IN bitmapDomain
Proof
  strip_tac >>
  mp_tac (Q.INST [`lo` |-> `n2w (bootDataRam+24):word64`,
                 `hi` |-> `n2w bootDataEnd:word64`]
    (INST_TYPE [alpha |-> ``:64``] aligned_interval_closed)) >>
  fs [bitmapDomain_def,bootDataRam_def,bootDataEnd_def,
      byte_aligned_def,aligned_w2n,w2n_n2w,dimword_64,dimindex_64]
QED
val _ = List.app (fn th => if null(hyp th) then ignore(check_thm th)
  else failwith "bitmap domain assumptions")
  [bitmap_word_domain,aligned_interval_closed,bitmap_domain_align_closed];
