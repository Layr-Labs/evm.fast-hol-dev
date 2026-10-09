(* Minimal, total declared gas reader from Guest/GasLimit.lean. *)
Theory initGas
Ancestors initParams
Libs preamble cv_transLib wordsLib

Definition inputByte_def:
  inputByte (input : word8 list) i =
    if i < LENGTH input then w2n (EL i input) else 0
End
val _ = cv_auto_trans inputByte_def;

Definition le32_def:
  le32 input i =
    inputByte input i + inputByte input (i+1) * 256 +
    inputByte input (i+2) * 65536 + inputByte input (i+3) * 16777216
End
val _ = cv_trans le32_def;

Definition le64_def:
  le64 input i = le32 input i + le32 input (i+4) * 4294967296
End
val _ = cv_trans le64_def;

Definition declaredGasLimit_def:
  declaredGasLimit input =
    let requestStart = 2 + le32 input 2;
        payloadStart = requestStart + le32 input requestStart
    in le64 input (payloadStart + 412)
End
val _ = cv_trans declaredGasLimit_def;

Theorem short_input_zero:
  declaredGasLimit [] = 0 /\ declaredGasLimit [21w;1w] = 0
Proof
  EVAL_TAC
QED

Theorem little_endian_regression:
  le32 [1w;2w;3w;4w] 0 = 67305985 /\
  le64 [255w;255w;255w;255w;255w;255w;255w;255w] 0 = 18446744073709551615
Proof
  EVAL_TAC
QED
