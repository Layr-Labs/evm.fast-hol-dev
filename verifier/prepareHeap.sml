(* Operator-only preparation: no participant data is read here. *)
load "initProofLibraryTheory";
load "cv_transLib";
(* Register concrete word arithmetic and dimension conversions for fixed EVAL. *)
load "wordsLib";
load "strictReplayLib";
load "certificateReplayLib";
PolyML.SaveState.saveState "verifier.heap";
