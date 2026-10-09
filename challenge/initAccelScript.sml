(* Concrete accelerator semantics transcribed from the pinned
   RiscvZkvm/Rv64/ZiskAccel.lean and Guest/AccelFfi.lean.
   No axioms or participant-selected oracle are used. *)
Theory initAccel
Ancestors initHost
Libs preamble wordsLib
Definition accGet_def:
  accGet d xs i = if i < LENGTH xs then EL i xs else d
End
Definition keccakRC_def:
  keccakRC : word64 list = [0x0000000000000001w; 0x0000000000008082w; 0x800000000000808Aw;
   0x8000000080008000w; 0x000000000000808Bw; 0x0000000080000001w;
   0x8000000080008081w; 0x8000000000008009w; 0x000000000000008Aw;
   0x0000000000000088w; 0x0000000080008009w; 0x000000008000000Aw;
   0x000000008000808Bw; 0x800000000000008Bw; 0x8000000000008089w;
   0x8000000000008003w; 0x8000000000008002w; 0x8000000000000080w;
   0x000000000000800Aw; 0x800000008000000Aw; 0x8000000080008081w;
   0x8000000000008080w; 0x0000000080000001w; 0x8000000080008008w]
End
Definition sha256K_def:
  sha256K : word32 list = [0x428a2f98w; 0x71374491w; 0xb5c0fbcfw; 0xe9b5dba5w;
   0x3956c25bw; 0x59f111f1w; 0x923f82a4w; 0xab1c5ed5w;
   0xd807aa98w; 0x12835b01w; 0x243185bew; 0x550c7dc3w;
   0x72be5d74w; 0x80deb1few; 0x9bdc06a7w; 0xc19bf174w;
   0xe49b69c1w; 0xefbe4786w; 0x0fc19dc6w; 0x240ca1ccw;
   0x2de92c6fw; 0x4a7484aaw; 0x5cb0a9dcw; 0x76f988daw;
   0x983e5152w; 0xa831c66dw; 0xb00327c8w; 0xbf597fc7w;
   0xc6e00bf3w; 0xd5a79147w; 0x06ca6351w; 0x14292967w;
   0x27b70a85w; 0x2e1b2138w; 0x4d2c6dfcw; 0x53380d13w;
   0x650a7354w; 0x766a0abbw; 0x81c2c92ew; 0x92722c85w;
   0xa2bfe8a1w; 0xa81a664bw; 0xc24b8b70w; 0xc76c51a3w;
   0xd192e819w; 0xd6990624w; 0xf40e3585w; 0x106aa070w;
   0x19a4c116w; 0x1e376c08w; 0x2748774cw; 0x34b0bcb5w;
   0x391c0cb3w; 0x4ed8aa4aw; 0x5b9cca4fw; 0x682e6ff3w;
   0x748f82eew; 0x78a5636fw; 0x84c87814w; 0x8cc70208w;
   0x90befffaw; 0xa4506cebw; 0xbef9a3f7w; 0xc67178f2w]
End
Definition blake2Sigma_def:
  blake2Sigma : num list list = [[0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15];
   [14; 10; 4; 8; 9; 15; 13; 6; 1; 12; 0; 2; 11; 7; 5; 3];
   [11; 8; 12; 0; 5; 2; 15; 13; 10; 14; 3; 6; 7; 1; 9; 4];
   [7; 9; 3; 1; 13; 12; 11; 14; 2; 6; 5; 10; 4; 0; 15; 8];
   [9; 0; 5; 7; 2; 4; 10; 15; 14; 1; 11; 12; 6; 8; 3; 13];
   [2; 12; 6; 10; 0; 11; 8; 3; 4; 13; 7; 5; 15; 14; 1; 9];
   [12; 5; 1; 15; 14; 13; 4; 10; 0; 7; 6; 3; 9; 2; 8; 11];
   [13; 11; 7; 14; 12; 1; 3; 9; 5; 0; 15; 4; 8; 6; 2; 10];
   [6; 15; 14; 9; 11; 3; 0; 8; 12; 2; 13; 7; 1; 4; 10; 5];
   [10; 2; 8; 4; 7; 6; 1; 5; 15; 11; 9; 14; 3; 12; 13; 0]]
End

Definition rhoOff_def:
  rhoOff x y : num = accGet 0 (accGet []
    [[0;36;3;41;18];[1;44;10;45;2];[62;6;43;15;61];
     [28;55;25;21;56];[27;20;39;8;14]] (x MOD 5)) (y MOD 5)
End
Definition keccakRound_def:
  keccakRound (rc:word64) st =
    let A = \x y. accGet 0w st (x MOD 5 + 5 * (y MOD 5));
        C = \x. A x 0 ?? A x 1 ?? A x 2 ?? A x 3 ?? A x 4;
        D = \x. C (x+4) ?? (C (x+1) #<< 1);
        B = \X Y. let xs = (X+3*Y) MOD 5; ys = X MOD 5 in
                   (A xs ys ?? D xs) #<< rhoOff xs ys;
        chi = \j. let X = j MOD 5; Y = j DIV 5 in
                    B X Y ?? (~(B (X+1) Y) && B (X+2) Y)
    in GENLIST (\j. if j = 0 then chi 0 ?? rc else chi j) 25
End
Definition keccakF_def:
  keccakF st = FOLDL (\s rc. keccakRound rc s) st keccakRC
End
Definition sha256W_def:
  sha256W (w:word32 list) = FOLDL (\acc t.
    if t < 16 then acc ++ [accGet 0w w t] else
      let x = accGet 0w acc (t-15); y = accGet 0w acc (t-2);
          s0 = (x #>> 7) ?? (x #>> 18) ?? (x >>> 3);
          s1 = (y #>> 17) ?? (y #>> 19) ?? (y >>> 10)
      in acc ++ [accGet 0w acc (t-16) + s0 + accGet 0w acc (t-7) + s1])
    [] (COUNT_LIST 64)
End
Definition sha256Compress_def:
  sha256Compress (hs:word32 list) w =
    let W = sha256W w;
        fin = FOLDL (\st t.
          let a = accGet 0w st 0; b = accGet 0w st 1;
              c = accGet 0w st 2; d = accGet 0w st 3;
              e = accGet 0w st 4; f = accGet 0w st 5;
              g = accGet 0w st 6; h = accGet 0w st 7;
              S1 = (e #>> 6) ?? (e #>> 11) ?? (e #>> 25);
              ch = (e && f) ?? (~e && g);
              T1 = h + S1 + ch + accGet 0w sha256K t + accGet 0w W t;
              S0 = (a #>> 2) ?? (a #>> 13) ?? (a #>> 22);
              maj = (a && b) ?? (a && c) ?? (b && c);
              T2 = S0 + maj
          in [T1+T2;a;b;c;d+T1;e;f;g]) (TAKE 8 hs) (COUNT_LIST 64)
    in GENLIST (\i. accGet 0w hs i + accGet 0w fin i)
         (MIN (LENGTH (TAKE 8 hs)) (LENGTH fin))
End
Definition leLimbsToNat_def:
  leLimbsToNat (ws:word64 list) = FOLDR (\w acc. acc * 2 ** 64 + w2n w) 0 ws
End
Definition natToLeLimbs_def:
  natToLeLimbs n x : word64 list = GENLIST (\i. n2w (x DIV 2 ** (64*i))) n
End
Definition blakeG_def:
  blakeG (v:word64 list) a b c d x y =
    let va = accGet 0w v a + accGet 0w v b + x;
        vd = (accGet 0w v d ?? va) #>> 32;
        vc = accGet 0w v c + vd;
        vb = (accGet 0w v b ?? vc) #>> 24;
        va' = va + vb + y;
        vd' = (vd ?? va') #>> 16;
        vc' = vc + vd';
        vb' = (vb ?? vc') #>> 63
    in LUPDATE vd' d (LUPDATE vc' c (LUPDATE vb' b (LUPDATE va' a v)))
End
Definition blake2bRound_def:
  blake2bRound idx v m =
    let s = accGet [] blake2Sigma (idx MOD 10);
        mi = \i. accGet 0w m (accGet 0 s i);
        v1 = blakeG v 0 4 8 12 (mi 0) (mi 1);
        v2 = blakeG v1 1 5 9 13 (mi 2) (mi 3);
        v3 = blakeG v2 2 6 10 14 (mi 4) (mi 5);
        v4 = blakeG v3 3 7 11 15 (mi 6) (mi 7);
        v5 = blakeG v4 0 5 10 15 (mi 8) (mi 9);
        v6 = blakeG v5 1 6 11 12 (mi 10) (mi 11);
        v7 = blakeG v6 2 7 8 13 (mi 12) (mi 13)
    in blakeG v7 3 4 9 14 (mi 14) (mi 15)
End
Definition powModAux_def:
  (powModAux m 0 b e = 1 MOD m) /\
  (powModAux m (SUC fuel) b e =
    if e = 0 then 1 MOD m else
      let h = powModAux m fuel (b*b MOD m) (e DIV 2) in
        if e MOD 2 = 1 then h * (b MOD m) MOD m else h)
End
Definition invMod_def:
  invMod x m = powModAux m 512 (x MOD m) (m-2)
End
Definition curveAdd_def:
  curveAdd p x1 y1 x2 y2 =
    let lam = (y2+p-y1) * invMod ((x2+p-x1) MOD p) p MOD p;
        x3 = (lam*lam+2*p-x1-x2) MOD p
    in (x3,(lam*((x1+p-x3) MOD p)+p-y1) MOD p)
End
Definition curveDbl_def:
  curveDbl p x1 y1 =
    let lam = (3*x1*x1 MOD p) * invMod (2*y1 MOD p) p MOD p;
        x3 = (lam*lam+2*p-x1-x1) MOD p
    in (x3,(lam*((x1+p-x3) MOD p)+p-y1) MOD p)
End
Definition curveAddL_def:
  curveAddL p nl pt1 pt2 =
    let r = curveAdd p (leLimbsToNat (TAKE nl pt1)) (leLimbsToNat (DROP nl pt1))
                      (leLimbsToNat (TAKE nl pt2)) (leLimbsToNat (DROP nl pt2))
    in natToLeLimbs nl (FST r) ++ natToLeLimbs nl (SND r)
End
Definition curveDblL_def:
  curveDblL p nl pt =
    let r = curveDbl p (leLimbsToNat (TAKE nl pt)) (leLimbsToNat (DROP nl pt))
    in natToLeLimbs nl (FST r) ++ natToLeLimbs nl (SND r)
End
Definition ptValid_def:
  ptValid p nl pt = (leLimbsToNat (TAKE nl pt) < p /\ leLimbsToNat (DROP nl pt) < p)
End
Definition complexAddL_def:
  complexAddL p nl f1 f2 =
    natToLeLimbs nl ((leLimbsToNat (TAKE nl f1) + leLimbsToNat (TAKE nl f2)) MOD p) ++
    natToLeLimbs nl ((leLimbsToNat (DROP nl f1) + leLimbsToNat (DROP nl f2)) MOD p)
End
Definition complexSubL_def:
  complexSubL p nl f1 f2 =
    natToLeLimbs nl ((leLimbsToNat (TAKE nl f1) + p - leLimbsToNat (TAKE nl f2)) MOD p) ++
    natToLeLimbs nl ((leLimbsToNat (DROP nl f1) + p - leLimbsToNat (DROP nl f2)) MOD p)
End
Definition complexMulL_def:
  complexMulL p nl f1 f2 =
    let x0 = leLimbsToNat (TAKE nl f1); x1 = leLimbsToNat (DROP nl f1);
        y0 = leLimbsToNat (TAKE nl f2); y1 = leLimbsToNat (DROP nl f2)
    in natToLeLimbs nl ((x0*y0+p*p-x1*y1) MOD p) ++
       natToLeLimbs nl ((x0*y1+x1*y0) MOD p)
End
Definition dwordsToU32s_def:
  dwordsToU32s (ws:word64 list) : word32 list =
    FLAT (MAP (\w. [w2w w; w2w (w >>> 32)]) ws)
End
Definition byteSwap32_def:
  byteSwap32 (x:word32) =
    ((x && 0x000000ffw) << 24) || ((x && 0x0000ff00w) << 8) ||
    ((x && 0x00ff0000w) >>> 8) || ((x && 0xff000000w) >>> 24)
End
Definition dwordsToU32sBE_def:
  dwordsToU32sBE ws = MAP byteSwap32 (dwordsToU32s ws)
End
Definition u32sToDwords_def:
  u32sToDwords ((lo:word32)::hi::rest) =
    (((w2w hi:word64) << 32) || w2w lo) :: u32sToDwords rest /\
  u32sToDwords _ = []
End
Definition wordsOfLeBytes_def:
  wordsOfLeBytes (b0::b1::b2::b3::b4::b5::b6::b7::rest) =
    wordOfLeBytes [b0;b1;b2;b3;b4;b5;b6;b7] :: wordsOfLeBytes rest /\
  wordsOfLeBytes _ = []
End
Definition leBytesOfWords_def:
  leBytesOfWords ws = FLAT (MAP leBytes ws)
End
Definition exactWords_def:
  exactWords (configuration:word8 list) bytes n =
    if configuration = [] /\ LENGTH bytes = 8*n then SOME (wordsOfLeBytes bytes) else NONE
End
Definition keccakfBytes_def:
  keccakfBytes c bs = OPTION_MAP (leBytesOfWords o keccakF) (exactWords c bs 25)
End
Definition sha256fBytes_def:
  sha256fBytes c bs = OPTION_MAP (\ws.
    leBytesOfWords (u32sToDwords (sha256Compress
      (dwordsToU32s (TAKE 4 ws)) (dwordsToU32sBE (DROP 4 ws)))) ++ DROP 32 bs)
    (exactWords c bs 12)
End
Definition arithModBytes_def:
  arithModBytes limbs c bs =
    case exactWords c bs (5*limbs) of NONE => NONE | SOME ws =>
      let a = leLimbsToNat (TAKE limbs ws);
          b = leLimbsToNat (TAKE limbs (DROP limbs ws));
          v = leLimbsToNat (TAKE limbs (DROP (2*limbs) ws));
          m = leLimbsToNat (TAKE limbs (DROP (3*limbs) ws))
      in if m = 0 then NONE else
        SOME (leBytesOfWords (TAKE (4*limbs) ws ++ natToLeLimbs limbs ((a*b+v) MOD m)))
End
Definition curveAddBytes_def:
  curveAddBytes prime limbs c bs =
    case exactWords c bs (4*limbs) of NONE => NONE | SOME ws =>
      let p1 = TAKE (2*limbs) ws; p2 = DROP (2*limbs) ws in
      if ptValid prime limbs p1 /\ ptValid prime limbs p2 /\
         leLimbsToNat (TAKE limbs p1) <> leLimbsToNat (TAKE limbs p2) then
        SOME (leBytesOfWords (curveAddL prime limbs p1 p2 ++ p2)) else NONE
End
Definition curveDblBytes_def:
  curveDblBytes prime limbs c bs =
    case exactWords c bs (2*limbs) of NONE => NONE | SOME pt =>
      if ptValid prime limbs pt /\ leLimbsToNat (DROP limbs pt) <> 0 then
        SOME (leBytesOfWords (curveDblL prime limbs pt)) else NONE
End
Definition complexBytes_def:
  complexBytes op prime limbs c bs =
    case exactWords c bs (4*limbs) of NONE => NONE | SOME ws =>
      let a = TAKE (2*limbs) ws; b = DROP (2*limbs) ws in
      if ptValid prime limbs a /\ ptValid prime limbs b then
        SOME (leBytesOfWords (op prime limbs a b ++ b)) else NONE
End
Definition blake2bBytes_def:
  blake2bBytes c bs =
    case exactWords c bs 33 of NONE => NONE | SOME ws =>
      case ws of [] => NONE | index::rest =>
        if w2n index < 10 then SOME (leBytesOfWords
          (index :: (blake2bRound (w2n index) (TAKE 16 rest) (DROP 16 rest) ++ DROP 16 rest)))
        else NONE
End
Definition secpP_def:
  secpP : num = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
End
Definition bn254P_def:
  bn254P : num = 21888242871839275222246405745257275088696311157297823662689037894645226208583
End
Definition bls12P_def:
  bls12P : num = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
End
Definition acceleratorBytes_def:
  acceleratorBytes name c bs =
    if name = «keccakf» then keccakfBytes c bs else
    if name = «sha256f» then sha256fBytes c bs else
    if name = «arith256mod» then arithModBytes 4 c bs else
    if name = «bn_arith256» then arithModBytes 4 c bs else
    if name = «bls_arith384» then arithModBytes 6 c bs else
    if name = «secpadd» then curveAddBytes secpP 4 c bs else
    if name = «secpdbl» then curveDblBytes secpP 4 c bs else
    if name = «bn_g1_add» then curveAddBytes bn254P 4 c bs else
    if name = «bn_g1_dbl» then curveDblBytes bn254P 4 c bs else
    if name = «bn_fp2_add» then complexBytes complexAddL bn254P 4 c bs else
    if name = «bn_fp2_sub» then complexBytes complexSubL bn254P 4 c bs else
    if name = «bn_fp2_mul» then complexBytes complexMulL bn254P 4 c bs else
    if name = «bls_g1_add» then curveAddBytes bls12P 6 c bs else
    if name = «bls_g1_dbl» then curveDblBytes bls12P 6 c bs else
    if name = «bls_fp2_add» then complexBytes complexAddL bls12P 6 c bs else
    if name = «bls_fp2_sub» then complexBytes complexSubL bls12P 6 c bs else
    if name = «bls_fp2_mul» then complexBytes complexMulL bls12P 6 c bs else
    if name = «blake2bround» then blake2bBytes c bs else
    NONE
End
