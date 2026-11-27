(* What this file guards: lib/calculus/contraction.ml keeps its binary sides in classes of equal
   variant keys and can skip trials, for speed. This is the earlier, simpler Contraction (one
   table from variant keys to stored sides, no skip), kept verbatim below this comment except for
   comments, as the reference of the randomized equivalence test in contraction_tests: the current
   module run with [~skip:false] must give the same answers, trials and exhaustions. Not part of
   the library; never change its code. *)

open Axiom_fuzzer
open Wire

type result = { clause : clause; rule : rule; using : int list }
(** Small retained premises simplify before they become given clauses. Targets are rigid; all
    conclusions carry ordinary resolution certificates. The inverse of a binary implication is also
    required to retire a rewritten target, and is returned separately from the logical inference
    parents. Under [Redundant] (the default of [create]; the engine's default is [Derive]) a rewrite
    is offered only when retiring the target is a redundancy deletion: the result and the inverse
    instance must both be smaller than the target, so a unit is never rewritten. *)

(** When an equivalence (two complementary two-literal clauses ~l' | r' and l' | ~r') may rewrite a
    literal l = l'.sigma of a target l | R into r = r'.sigma and retire the target. The target
    follows from the result r | R and the inverse instance l | ~r, so the retirement is a redundancy
    deletion (Bachmair-Ganzinger) only when both are smaller than the target: l > r and
    [{~r} <mul R], i.e. some other literal of the target exceeds ~r. *)
type equivalence =
  | Redundant
      (** Both conditions (the default of [create]): a unit target never qualifies, since l | ~r is
          larger than l. *)
  | Legacy
      (** Only l > r, units included: an earlier rule of this engine, refutationally incomplete (a
          retired unit's inferences are lost: the inverse, with ~r selected, re-derives l from r
          only for l to be rewritten again, so Passive can empty on an unsatisfiable input). It is
          also Vampire's ForwardLiteralRewriting condition, which the Vampire slice members keep.
          Otherwise reachable only through the evaluation hook [AXIOM_EQUIVALENCE=legacy], for A/B
          runs. *)
  | Derive
      (** [Redundant], and a rewrite that only [Legacy] would make is offered by {!derive} as an
          ordinary consequence (the resolvent with the side clause) while the target stays: no
          deletion, so complete. The engine's default ([Engine.default_config]). *)

let equivalence_name = function Redundant -> "redundant" | Legacy -> "legacy" | Derive -> "derive"

type key = { hash : int; value : clause * int list }
(** A variant key ([Variant_index.key]) with its [Tbl.Hash.clause_ints] hash, computed once: a
    binary side's inverse lookup used to hash the whole key at every trial. Equal values have equal
    hashes, so [Keys] answers exactly as a [Tbl.Clause_ints] table, in the same bucket order. *)

module Keys = Hashtbl.Make (struct
  type t = key

  let equal a b = a == b || (Int.equal a.hash b.hash && Tbl.Equal.clause_ints a.value b.value)
  let hash k = k.hash
end)

let key value = { hash = Tbl.Hash.clause_ints value; value }

type side = {
  opposite : clause;  (** the complement of the side clause *)
  opposite_key : key;  (** its variant key *)
  mutable seen : int;  (** the [epoch] at which [ids] was read; [-1]: never *)
  mutable ids : int list;  (** [equivalents]' entry for [opposite_key] at [seen] *)
}

type t = {
  units : Index.t;
  binary : Index.t;  (** Both index the side clauses as stored; see [indexed]. *)
  equivalents : int list Keys.t;
  steps : step Tbl.Int.t;
  inverse : side Tbl.Int.t;
      (** Per binary side clause, functions of the stored clause alone (proof ids are never reused),
          computed once at [add]. *)
  mutable touched : key list;
      (** [equivalents] keys added to, or holding a removed id, since the last [compact]; every
          other entry is still sorted, duplicate-free and made of stored ids (repeats allowed) *)
  mutable epoch : int;  (** changes whenever an [equivalents] entry may have changed *)
  mutable unit_deleted : int;
  mutable literal_rewritten : int;
  mutable literal_justified : int;
      (** Rewrites whose retirement is a redundancy deletion: every one under [Redundant]; under
          [Legacy] the ones that also meet the redundancy condition (a diagnostic count). *)
  mutable literal_units : int;  (** Rewrites of a unit target (only under [Legacy]). *)
  mutable literal_derived : int;  (** Consequences offered by {!derive} (only under [Derive]). *)
  mutable trials : int;
  mutable exhausted : int;
  order : Ordering.order;
  equivalence : equivalence;
}

let create ?(order = Ordering.standard) ?(equivalence = Redundant) () =
  {
    units = Index.create ();
    binary = Index.create ();
    equivalents = Keys.create 32;
    steps = Tbl.Int.create 64;
    inverse = Tbl.Int.create 64;
    touched = [];
    epoch = 0;
    unit_deleted = 0;
    literal_rewritten = 0;
    literal_justified = 0;
    literal_units = 0;
    literal_derived = 0;
    trials = 0;
    exhausted = 0;
    order;
    equivalence;
  }

let complement clause = List.map (fun l -> { l with positive = not l.positive }) clause

(* A side clause is matched with its own variables, and only a found substitution is renamed into
   scope 1 ([into_side]), where every trial used to copy the side clause into scope 1 first. Stored
   clauses are normalized, so all their variables are (0, i) and the renaming (0, i) -> (1, i) is
   a bijection: matching gives the same bindings in the same order, and [apply] on the side's
   other literal (all of whose variables the pivot binds) gives the same replacement. A clause with
   other variables (never stored by the engine) is indexed as its scope-1 copy, as before; there
   [into_side] changes nothing. *)
let indexed (s : step) =
  if List.for_all (fun ((a, _) : variable) -> a = 0) (Wire.variables s.clause) then s
  else { s with clause = Clause.scope 1 s.clause }

let into_side sigma = List.map (fun (((_, i) : variable), term) -> ((1, i), term)) sigma

let add t (s : step) =
  match s.clause with
  | [ _ ] ->
      Index.add t.units (indexed s);
      Tbl.Int.replace t.steps s.id s
  | [ _; _ ] ->
      Index.add t.binary (indexed s);
      Tbl.Int.replace t.steps s.id s;
      let k = key (Variant_index.key s.clause) in
      Keys.replace t.equivalents k (s.id :: Option.value ~default:[] (Keys.find_opt t.equivalents k));
      t.touched <- k :: t.touched;
      t.epoch <- t.epoch + 1;
      let opposite = complement s.clause in
      Tbl.Int.replace t.inverse s.id
        { opposite; opposite_key = key (Variant_index.key opposite); seen = -1; ids = [] }
  | _ -> ()

let remove t id =
  Index.remove t.units id;
  Index.remove t.binary id;
  (match Tbl.Int.find_opt t.steps id with
  | Some ({ clause = [ _; _ ]; _ } as s) ->
      (* Its [equivalents] entry, recomputed rather than kept for every stored side. *)
      t.touched <- key (Variant_index.key s.clause) :: t.touched
  | _ -> ());
  Tbl.Int.remove t.steps id;
  Tbl.Int.remove t.inverse id

let normalize t ids =
  match List.filter (Tbl.Int.mem t.steps) ids |> List.sort_uniq compare with
  | [] -> None
  | ids -> Some ids

(* Every [equivalents] entry normalized: the reference for [compact] in the unit tests. *)
let compact_all t =
  Index.compact_all t.units;
  Index.compact_all t.binary;
  t.touched <- [];
  t.epoch <- t.epoch + 1;
  Keys.filter_map_inplace (fun _ ids -> normalize t ids) t.equivalents

(* Normalizing an untouched entry would give it back unchanged, so only the touched ones are
   normalized; replacing or removing a key in place keeps the order of the others. *)
let compact t =
  Index.compact t.units;
  Index.compact t.binary;
  let touched = t.touched in
  t.touched <- [];
  if touched <> [] then t.epoch <- t.epoch + 1;
  (* With at least as many touched marks as entries, normalizing every entry costs no more. *)
  if List.compare_length_with touched (Keys.length t.equivalents) >= 0 then
    Keys.filter_map_inplace (fun _ ids -> normalize t ids) t.equivalents
  else
    let seen = Keys.create 16 in
    List.iter
      (fun key ->
        if not (Keys.mem seen key) then (
          Keys.add seen key ();
          match Keys.find_opt t.equivalents key with
          | None -> ()
          | Some ids -> (
              match normalize t ids with
              | None -> Keys.remove t.equivalents key
              | Some ids -> Keys.replace t.equivalents key ids)))
      touched

let rec apply sigma = function
  | V v as x -> Option.value ~default:x (Sym.assoc_opt v sigma)
  | Fn (f, xs) -> Fn (f, List.map (apply sigma) xs)

(* [binary]: also rewrite with binary sides and their inverses (literal rewriting); off, only
   unit deletion. *)
(* [accept]: which binary rewrites the search offers: [`Rule] the ones [t.equivalence] allows
   ([Derive] as [Redundant]); [`Unjustified] only the ones the redundancy condition refuses
   ({!derive}). *)
let search ~accept ?(budget = 1024) ?(binary = true) ~guard t (target : step) =
  let exception Exhausted in
  let left = ref budget in
  let tick () =
    guard ();
    decr left;
    if !left < 0 then raise Exhausted
  in
  let ys = Clause.scope 2 target.clause in
  (* Fingerprint compatibility is necessary for matching scoped-apart literals
     (it is the unification prefilter of Index, and E atoms are checked in both
     orientations), so rejected postings could never match. They still consume
     their per-posting tick, but no longer the inner Subsumption.atom ticks or
     the inverse-lookup ticks a failed match used to spend, so the budget
     reaches further postings than before: the same contractions are found
     whenever both budgets suffice, and possibly more otherwise. *)
  let fingerprints = List.map (fun (l : literal) -> Index.Fingerprint.atom l.atom) ys in
  (* Rewriting literal j = l of the target l | R into r retires the target, which follows from
     the result r | R and the inverse instance l | ~r ([equivalence]). l > r is checked at the
     match; [justified] is the second condition, {~r} <mul R: some other literal of the target
     exceeds ~r (a literal of R equal to ~r would make the result a tautology, which emission
     drops). The ordering is stable under substitution, so the condition holds for every ground
     instance. A unit target never qualifies. *)
  let justified j replacement =
    let complement = { replacement with positive = not replacement.positive } in
    let rec exceeds k = function
      | [] -> false
      | other :: rest ->
          (k <> j && Ordering.literal_greater ~order:t.order other complement)
          || exceeds (k + 1) rest
    in
    exceeds 0 ys
  in
  let redundant = t.equivalence <> Legacy in
  let derived = accept = `Unjustified in
  (* Every posting costs one tick, as before; only a posting that reaches the matcher also polls
     [guard] (the engine's cooperative check), so skipped postings no longer pay a check each. The
     budget, and so every answer and every exhaustion, is unchanged. *)
  let query index f =
    List.find_map
      (fun (j, l, fp) ->
        Index.bucket index l
        |> List.find_map (fun p ->
            decr left;
            if !left < 0 then raise Exhausted;
            if p.Index.step.id = target.id || not (Index.live p) then None
            else if not (Index.fingerprint_matches index l.atom fp p) then None
            else (
              guard ();
              f j l p)))
      (List.mapi (fun j l -> (j, l, List.nth fingerprints j)) ys)
  in
  let match_atom pattern atom k =
    let attempt atom =
      try k (Subsumption.atom ~guard:tick [] pattern atom) with Subsumption.No_match -> None
    in
    match attempt atom with
    | Some _ as found -> found
    | None -> ( match atom with E (s, t) -> attempt (E (t, s)) | _ -> None)
  in
  try
    match
      if derived then None
      else
        query t.units (fun j l p ->
            t.trials <- t.trials + 1;
            let pivot = List.hd p.Index.step.clause in
            match_atom pivot.atom l.atom (fun sigma ->
                t.unit_deleted <- t.unit_deleted + 1;
                Some
                  {
                    clause = Clause.remove j ys;
                    rule = Resolve (p.step.id, 0, target.id, j, into_side sigma);
                    using = [ p.step.id ];
                  }))
    with
    | Some _ as found -> found
    | None when not binary -> None
    | None when redundant && (not derived) && List.compare_length_with ys 2 < 0 -> None
    | None ->
        query t.binary (fun j l p ->
            t.trials <- t.trials + 1;
            let side = p.Index.step in
            let lookup k = Option.value ~default:[] (Keys.find_opt t.equivalents k) in
            let opposite, ids =
              match Tbl.Int.find_opt t.inverse side.id with
              | Some cached ->
                  (* [equivalents] is unchanged since the last lookup: the same entry. *)
                  if cached.seen <> t.epoch then (
                    cached.ids <- lookup cached.opposite_key;
                    cached.seen <- t.epoch);
                  (cached.opposite, cached.ids)
              | None ->
                  let stored =
                    match Tbl.Int.find_opt t.steps side.id with Some s -> s | None -> side
                  in
                  let opposite = complement stored.clause in
                  (opposite, lookup (key (Variant_index.key opposite)))
            in
            let inverse =
              ids
              |> List.find_map (fun id ->
                  tick ();
                  match Tbl.Int.find_opt t.steps id with
                  | Some other when id <> target.id && Variant_index.variants other.clause opposite
                    ->
                      Some id
                  | _ -> None)
            in
            Option.bind inverse (fun inverse ->
                let xs = side.clause in
                let pivot = List.nth xs p.literal and rhs = List.nth xs (1 - p.literal) in
                if
                  not
                    (List.for_all
                       (fun v -> List.mem v (Wire.variables [ pivot ]))
                       (Wire.variables [ rhs ]))
                then None
                else
                  match_atom pivot.atom l.atom (fun sigma ->
                      let replacement = Clause.map_literal (apply sigma) rhs in
                      if not (Ordering.literal_greater ~order:t.order l replacement) then None
                      else
                        (* Under [Legacy] the condition is only counted: the same rewrites, ticks
                           and answers as before. *)
                        let deletion = justified j replacement in
                        if derived then
                          if deletion then None
                          else (
                            t.literal_derived <- t.literal_derived + 1;
                            Some
                              {
                                clause = Clause.replace j replacement ys;
                                rule = Resolve (side.id, p.literal, target.id, j, into_side sigma);
                                using = [ side.id ];
                              })
                        else if redundant && not deletion then None
                        else (
                          t.literal_rewritten <- t.literal_rewritten + 1;
                          if deletion then t.literal_justified <- t.literal_justified + 1;
                          if List.compare_length_with ys 1 = 0 then
                            t.literal_units <- t.literal_units + 1;
                          Some
                            {
                              clause = Clause.replace j replacement ys;
                              rule = Resolve (side.id, p.literal, target.id, j, into_side sigma);
                              using = [ side.id; inverse ];
                            }))))
  with Exhausted ->
    t.exhausted <- t.exhausted + 1;
    None

let find ?budget ?binary ~guard t target = search ~accept:`Rule ?budget ?binary ~guard t target

(** Under [Derive]: the first binary rewrite of [target] that [Legacy] would make and the redundancy
    condition refuses, as a consequence to add while the target stays (its [using] is the side
    clause alone: nothing is retired). [None] under the other rules. *)
let derive ?budget ~guard t target =
  if t.equivalence <> Derive then None
  else search ~accept:`Unjustified ?budget ~binary:true ~guard t target
