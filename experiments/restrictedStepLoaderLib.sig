signature restrictedStepLoaderLib = sig
  val load : unit -> unit
  val register : (Term.term -> Thm.thm) * (string -> Thm.thm) -> unit
  val riscv_step : Term.term -> Thm.thm
  val riscv_step_hex : string -> Thm.thm
end
