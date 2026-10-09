Theory initAccelChecks
Ancestors initAccel cv_std
Libs preamble cv_transLib wordsLib
fun function_let_conv tm =
  case strip_comb tm of
    (c,[f,x]) =>
      if same_const c boolSyntax.let_tm andalso can dom_rng (type_of x)
      then pairLib.let_CONV tm else NO_CONV tm
  | _ => NO_CONV tm;
val _ = cv_auto_trans (CONV_RULE (DEPTH_CONV function_let_conv) keccakRound_def);
val _ = cv_auto_trans keccakF_def;
val _ = cv_auto_trans sha256Compress_def;
fun closed name th = if null (hyp th) then save_thm (name,check_thm (EQT_ELIM th))
  else failwith "accelerator test has assumptions";
Definition keccakKat_def:
  keccakKat <=> TAKE 4 (keccakF (GENLIST (\j. if j = 0 then 1w else
    if j = 16 then 0x8000000000000000w else 0w) 25)) =
    [0x3c23f7860146d2c5w;0xc003c7dcb27d7e92w;0x3b2782ca53b600e5w;0x70a4855d04d8fa7bw]
End
val _ = cv_auto_trans keccakKat_def;
val _ = closed "keccakKat_checked" (cv_eval ``keccakKat``);
Definition sha256Kat_def:
  sha256Kat <=> sha256Compress
    [0x6a09e667w;0xbb67ae85w;0x3c6ef372w;0xa54ff53aw;
     0x510e527fw;0x9b05688cw;0x1f83d9abw;0x5be0cd19w]
    (0x80000000w :: REPLICATE 15 0w) =
    [0xe3b0c442w;0x98fc1c14w;0x9afbf4c8w;0x996fb924w;
     0x27ae41e4w;0x649b934cw;0xa495991bw;0x7852b855w]
End
val _ = cv_auto_trans sha256Kat_def;
val _ = closed "sha256Kat_checked" (cv_eval ``sha256Kat``);
Theorem accelerator_boundaries:
  acceleratorBytes «unknown» [] [] = NONE /\
  acceleratorBytes «keccakf» [0w] (REPLICATE 200 0w) = NONE /\
  acceleratorBytes «sha256f» [] [] = NONE /\
  acceleratorBytes «arith256mod» [] (REPLICATE 160 0w) = NONE /\
  acceleratorBytes «secpdbl» [] (REPLICATE 64 0w) = NONE /\
  acceleratorBytes «blake2bround» [] (leBytesOfWords (10w::REPLICATE 32 0w)) = NONE
Proof
  EVAL_TAC
QED
Theorem modular_arithmetic_vector:
  arithModBytes 1 [] (leBytesOfWords [7w;9w;2w;13w;0w]) =
    SOME (leBytesOfWords [7w;9w;2w;13w;0w]) /\
  curveAddL 17 1 [1w;2w] [3w;4w] = [14w;2w] /\
  complexMulL 17 1 [1w;2w] [3w;4w] = [12w;10w]
Proof
  EVAL_TAC
QED
