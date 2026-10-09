(* Fixed, operator-built generic proof library for participant certificates.
   This theory contains no baseline-specific compilation or Certificate fact. *)
Theory initProofLibrary
Ancestors
  initChallenge
  initChallengePancake
  initChallengeTotal
  initStackRank
  initRestrictedEncoder
  initEncoderExecution
  initCompilerMachine
  initFfiBoundary
  initCodeMemory
  initWordListMemory
  initBootstrapMemory
  initBootstrapStores
  panWordCv
  backendRiscvCv
  numSortCv
  decoderTreeHint
  crepNoInline
  pancakeBackendBridge
  pancakeCorrectnessBridge
  panMainOrder
Libs preamble

(* The tracing writer eta-contracts recursive dispatch and uses I for the
   identity branch. Resolve this symbolic equation without evaluating TAILREC. *)
Theorem tailrec_dispatch:
  !(f:'a -> 'a + 'b) x.
    While$TAILREC f x = sum$sum_CASE (f x) (While$TAILREC f) combin$I
Proof
  rpt gen_tac >> ONCE_REWRITE_TAC [WhileTheory.TAILREC] >>
  Cases_on `f x` >> simp [combinTheory.I_THM]
QED
