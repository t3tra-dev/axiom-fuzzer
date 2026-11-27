type report = { steps : int; axioms : int; seconds : float }
(** Fail-closed, pure replay of portable proof data. Uses neither the mutable unifier, search
    calculus, search clausifier nor search clause normalizer. *)

val check : ?guard:(unit -> unit) -> Theory.t -> Wire.certificate -> (report, string) result
val normalize : Wire.clause -> Wire.clause
val input_clauses : ?guard:(unit -> unit) -> ?mode:Wire.cnf_mode -> Wire.axiom -> Wire.clause list
val rocq_document : Theory.t -> Wire.certificate -> (string, string) result

val derive :
  inputs:(int * Wire.clause list) list ->
  steps:Wire.step list ->
  Wire.rule ->
  (Wire.clause, string) result
(** Candidate construction only; acceptance always requires [check]. *)
