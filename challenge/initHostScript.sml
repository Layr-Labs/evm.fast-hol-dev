(* Host framing and shared-memory oracle from Guest/Model and
   InitE/SourceSemantics. Accelerator semantics remain to be instantiated. *)
Theory initHost
Ancestors initParams ffi
Libs preamble wordsLib

Type host_memory = ``:word64 -> word8 option``

Definition leBytes_def:
  leBytes (w : word64) =
    GENLIST (\i. n2w (w2n w DIV 256 ** i) : word8) 8
End
Definition wordOfLeBytes_def:
  wordOfLeBytes (bs : word8 list) : word64 =
    n2w (FOLDR (\b n. n * 256 + w2n b) 0 bs)
End
Definition hostInputBytes_def:
  hostInputBytes input =
    REPLICATE 8 (0w:word8) ++ leBytes (n2w (LENGTH input)) ++ input ++
    REPLICATE ((8 - LENGTH input MOD 8) MOD 8) 0w
End
Definition guestHostMemory_def:
  guestHostMemory input (address : word64) =
    if inputStart <= w2n address /\ w2n address < inputEnd then
      let offset = w2n address - inputStart;
          bytes = hostInputBytes input in
      SOME (if offset < LENGTH bytes then EL offset bytes else 0w)
    else if outputStart <= w2n address /\ w2n address < outputEnd then SOME 0w
    else NONE
End
Definition sharedWidth_def:
  sharedWidth (configuration : word8 list) =
    case configuration of [w] => if w = 0w then 8 else w2n w | _ => 0
End
Definition readHost_def:
  (readHost (host : host_memory) [] = SOME []) /\
  (readHost host (a::rest) =
    case host a of NONE => NONE | SOME b =>
      case readHost host rest of NONE => NONE | SOME bs => SOME (b::bs))
End
Definition writeHost_def:
  writeHost (host : host_memory) (address : word64) (values : word8 list) current =
    let offset = w2n (current - address) in
      if address <=+ current /\ offset < LENGTH values then SOME (EL offset values)
      else host current
End
Definition terminalOracle_def:
  terminalOracle accelerator name (host : host_memory) configuration bytes =
    case name of
      SharedMem MappedRead =>
        let width = sharedWidth configuration;
            address = wordOfLeBytes bytes in
        (case readHost host (GENLIST (\i. address + n2w i) width) of
           NONE => Oracle_final FFI_failed
         | SOME values => Oracle_return host (values ++ REPLICATE (LENGTH bytes - width) 0w))
    | SharedMem MappedWrite =>
        let count = LENGTH bytes - 8;
            values = TAKE count bytes;
            address = wordOfLeBytes (DROP count bytes) in
        if EVERY (\i. IS_SOME (host (address + n2w i))) (COUNT_LIST count) then
          Oracle_return (writeHost host address values) bytes
        else Oracle_final FFI_failed
    | ExtCall name =>
        if name = «halt» \/ name = «trap» then Oracle_final FFI_failed
        else case accelerator name configuration bytes of
          NONE => Oracle_final FFI_failed
        | SOME result => Oracle_return host result
End

Theorem terminal_calls:
  terminalOracle accelerator (ExtCall «halt») host conf bytes = Oracle_final FFI_failed /\
  terminalOracle accelerator (ExtCall «trap») host conf bytes = Oracle_final FFI_failed
Proof
  simp [terminalOracle_def]
QED
Theorem host_framing_regression:
  TAKE 18 (hostInputBytes [171w;205w]) =
    [0w;0w;0w;0w;0w;0w;0w;0w;2w;0w;0w;0w;0w;0w;0w;0w;171w;205w] /\
  guestHostMemory [] (n2w outputStart) = SOME 0w /\
  guestHostMemory [] (n2w outputEnd) = NONE
Proof
  EVAL_TAC
QED
