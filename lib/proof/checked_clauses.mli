exception Reject of string
(** Private adapter for the extracted Source/CNF checker and normalizer. Neither operation calls the
    search clausifier or search clause normalizer. *)

val normalize : Wire.clause -> Wire.clause

val prepare_input :
  ?guard:(unit -> unit) ->
  ?mode:Wire.cnf_mode ->
  Wire.axiom ->
  Kernel_checker.prepared_axiom * Wire.clause list

val input_clauses : ?guard:(unit -> unit) -> ?mode:Wire.cnf_mode -> Wire.axiom -> Wire.clause list
