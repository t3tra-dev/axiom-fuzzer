type t

module Schema : sig
  type bounds = { max_size : int; parameters : int }
  type 'p t

  val create :
    ?guide:(Source.t -> Source.formula -> 'p option) ->
    name:string ->
    revision:string ->
    encode:('p -> string) ->
    decode:(string -> 'p option) ->
    enumerate:(Signature.t -> bounds option -> 'p Seq.t) ->
    expand:(Source.t -> 'p -> Source.formula) ->
    check:(Signature.t -> 'p -> Wire.source -> bool) ->
    unit ->
    'p t
  (** Parameters are immutable, portable values, not arena IDs. [encode]/[decode] must roundtrip
      canonically. [None] bounds requests exhaustive enumeration; each sequence step must terminate.
      Every invocation must return a fresh, deterministic stream. Callbacks may run in different
      Domains and must not share mutable state. [expand] returns a closed formula in the supplied
      arena.

      [check] independently validates the parameter and raw axiom, without calling [expand]. It is
      part of the trusted theory definition, not a Rocq-proved checker. No callback is loaded from a
      certificate. Change [revision] whenever semantics, parameter encoding or enumeration order
      changes. *)

  val key : 'p t -> Wire.schema
end

val register_schema : t -> 'p Schema.t -> t
(** Add a schema to an immutable manifest. Duplicate/reserved names are rejected. The returned
    theory shares the original arena; [copy] creates a fresh arena. *)

val instantiate_schema : t -> id:int -> 'p Schema.t -> 'p -> Wire.axiom
(** Expand through the definition registered in [t]. Acceptance still requires [validate_axiom] or
    [Kernel.check]; generation alone is not validation. *)

val copy : ?preserve_arena:bool -> t -> t
(** Share the immutable manifest, signature and schema definitions, with an independent Source
    arena. By default the arena is empty; [preserve_arena] copies its existing nodes in allocation
    order, preserving Boolean normalization order without rebuilding formulas. Handles from [t] are
    not portable in either mode. This does not parse or revalidate the theory. *)

val names : string list
val create : string -> t
val custom : name:string -> Signature.t -> (string * Wire.source) list -> t

val of_definitions : name:string -> Definitions.t -> (string * Wire.source) list -> t
(** Close each formula over its free parameters and expand the definitions before forming the
    manifest. Certificates contain only the base language and use the existing kernel. The theory
    keeps the definitions and the closed original formulas; construction checks with the extracted
    [Source_checker.expansions_match] that the manifest axioms are what the originals expand to. *)

val definitions :
  t ->
  (Source_checker.function_definitions
  * Source_checker.predicate_definitions
  * (string * Wire.source) list)
  option
(** For a theory made by [of_definitions]: the definitions and the closed original axioms, by label.
    [None] otherwise. *)

val of_enumerator : name:string -> revision:string -> step:(int -> Wire.source option) -> t
(** A recursively enumerable axiom presentation over the countable string vocabulary. [step n] must
    terminate and deterministically return either a closed axiom or [None]. Quiet steps do not end
    enumeration. Every intended axiom must occur at some finite index; duplicates are allowed, and
    an empty theory may return [None] forever. A bounded simulation of a recognizer can supply these
    observations; do not wait for its next output in one call. The enumeration defines the theory
    and is rerun when checking its finite index witnesses. It is not loaded from certificates.
    Change [revision] when its meaning or indexing changes. Callbacks must be safe to share in
    Domains. *)

val instantiate_enumerated : t -> id:int -> int -> Wire.axiom
(** Construct the axiom emitted at this stage; reject quiet stages. The normal independent proof
    checker still validates the resulting certificate. *)

val name : t -> string
val arena : t -> Source.t
val fixed : t -> Wire.axiom list
val schemas : t -> Wire.schema list

val manifest : t -> Source_checker.theory
(** Immutable authority consumed directly by the extracted Source kernel. *)

val arity : Wire.schema -> int
(** Principal formula variables for built-in schemas. Registered schemas define their own parameter
    types and enumeration; they have no formula arity. *)

val instantiate : t -> id:int -> Wire.schema -> Source.formula -> Wire.axiom
val validate_axiom : t -> Wire.axiom -> bool

type parameter
(** Opaque parameter used uniformly by the scheduler and reference worker. *)

val enumerate : t -> ?bounds:Schema.bounds -> Wire.schema -> parameter option Seq.t
(** One finite observation per step. [Some p] is a candidate, [None] yields the slot to other work,
    and [Seq.Nil] ends a finite stream. Enumerated theories use [bounds.max_size] as the number of
    observation stages, starting at zero. *)

val guided_parameter : t -> Wire.schema -> Source.formula -> parameter option
val instantiate_parameter : t -> id:int -> Wire.schema -> parameter -> Wire.axiom

val parameter_info : t -> Wire.schema -> parameter -> int * int
(** Formula size and additional free variables. Both are zero for opaque custom parameters, for
    which these formula-specific metrics are not measured. *)

val parameter_text : t -> parameter -> string
