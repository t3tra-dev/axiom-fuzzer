type t
(** Elaborate portable inferences into Rocq primitive steps. This builder does not validate Source
    provenance; certificate acceptance belongs to Kernel. The mutable tables and append-only
    database cannot be accessed by callers. Discard a builder if [record] raises. *)

val create : ?components:Wire.clause list -> (int * Wire.clause list) list -> t
val record : t -> Wire.step -> expected:Wire.clause -> apply:(Wire.term -> Wire.term) -> unit

val inputs : t -> Rocq_checker.clause list
(** Immutable views in certificate order, also suitable for differential checks. *)

val certificate : t -> Rocq_checker.certificate
val encoding_valid : t -> bool
val check : t -> bool

val check_theory :
  ?avatar:Wire.avatar_certificate ->
  guard:(unit -> unit) ->
  manifest:Source_checker.theory ->
  name:string ->
  Kernel_checker.prepared_axiom list ->
  t ->
  bool

val document :
  ?avatar:Wire.avatar_certificate ->
  manifest:Source_checker.theory ->
  name:string ->
  Kernel_checker.prepared_axiom list ->
  t ->
  string
