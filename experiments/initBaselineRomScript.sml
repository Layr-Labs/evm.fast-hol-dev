(* A candidate ROM assembled from checked compiler and bootstrap results.
   This theory does not yet prove the challenge Certificate. *)
Theory initBaselineRom
Ancestors initArtifacts initBootstrap
Libs preamble cv_transLib wordsLib
val _ = Feedback.set_trace "TheoryPP.include_html_docs" 0;
val _ = cv_memLib.use_long_names := true;
Definition bootWordBytes_def:
  bootWordBytes (w:word64) =
    GENLIST (\i. n2w (w2n w DIV 2 ** (8*i)) : word8) 8
End
Definition baselineInitData_def:
  baselineInitData = FLAT (MAP bootWordBytes
    ([n2w sourceBase; n2w stackStart; n2w ramEnd] ++ compiledBitmaps))
End
Definition baselineRom_def:
  baselineRom = bootstrapBytes ++
    REPLICATE (baselineNativePc - initialPc - LENGTH bootstrapBytes) 0w ++
    compiledBytes ++
    REPLICATE (bootDataRom - baselineNativePc - LENGTH compiledBytes) 0w ++
    baselineInitData
End
val _ = cv_auto_trans baselineRom_def;
fun save_closed name th = if null (hyp th) then save_thm (name,check_thm th)
  else failwith "ROM theorem has assumptions";
val _ = save_closed "initial_data_length"
  (EQT_ELIM (cv_eval ``LENGTH baselineInitData = bootDataEnd - bootDataRam``));
val _ = save_closed "baseline_rom_length"
  (EQT_ELIM (cv_eval ``LENGTH baselineRom = 950344``));
val _ = save_closed "native_fits_before_fixed_buffer"
  (EQT_ELIM (cv_eval ``baselineNativePc + LENGTH compiledBytes <= 0x800ddd08``));
val _ = save_closed "native_ends_at_fixed_buffer"
  (EQT_ELIM (cv_eval ``baselineNativePc + LENGTH compiledBytes = 0x800ddd08``));
val _ = save_closed "native_image_in_rom"
  (EQT_ELIM (cv_eval ``TAKE (LENGTH compiledBytes)
    (DROP (baselineNativePc-initialPc) baselineRom) = compiledBytes``));
val _ = save_closed "data_image_in_rom"
  (EQT_ELIM (cv_eval ``DROP (bootDataRom-initialPc) baselineRom = baselineInitData``));
val result = cv_eval_raw ``baselineRom``;
val _ = check_thm result;
val stream = BinIO.openOut "baseline-rom.bin";
fun emit tm = if cvSyntax.is_cv_pair tm then
  let val (n,rest) = cvSyntax.dest_cv_pair tm
      val b = numSyntax.int_of_term (cvSyntax.dest_cv_num n)
  in if 0 <= b andalso b < 256 then
       (BinIO.output1(stream,Word8.fromInt b);emit rest)
     else failwith "ROM byte out of range" end
  else if aconv tm (cvSyntax.mk_cv_num numSyntax.zero_tm) then ()
  else failwith "ROM byte list malformed";
val _ = emit (rand (rconc result));
val _ = BinIO.closeOut stream;
