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

(* The binary sides whose variant keys are equal form a class. A side looks up its inverse
   candidates in the class of its complement's key, which it holds directly: the class's [ids] are
   what a table from variant keys to stored sides would hold for that key (the same list, in the
   same order, [] for no entry; tests/regression/contraction_reference.ml keeps that table as the
   reference), so no trial hashes a key or waits for a cache to be refreshed. *)
type klass = {
  value : key;
  mutable ids : int list;
      (** the stored binary sides with this variant key: added ids first, removed ids until
          [compact], which sorts the list and removes duplicates; [] when there is none *)
  mutable sides : int list;
      (** the binary sides whose complement has this key, in any order (removed ids, and ids added
          again with another clause, until [compact]) *)
  mutable mark : int;  (** the [compact] that last normalized the class *)
}

type side = {
  opposite : clause;  (** the complement of the side clause *)
  opposite_key : key;  (** its variant key *)
  own : klass;  (** the class of the side's key *)
  opp : klass;  (** the class of [opposite_key]: its [ids] are the inverse candidates *)
  features : Clause.feature list;  (** the keys of its literals' postings in [binary] *)
  mutable counted : bool;
      (** [opp.ids] is not empty: the side's postings are counted in [partnered] *)
  mutable variants : (step * bool) list;
      (** [Variant_index.variants] of [opposite] and the stored clauses already tried as its
          inverse, by the stored step (physically): a pure function of the two clauses *)
}

type t = {
  units : Index.t;
  binary : Index.t;  (** Both index the side clauses as stored; see [indexed]. *)
  classes : klass Keys.t;
      (** the classes that have [ids] or [sides]; a class with neither leaves at [compact] *)
  steps : step Tbl.Int.t;
  inverse : side Tbl.Int.t;
      (** Per binary side clause, functions of the stored clause alone (proof ids are never reused),
          computed once at [add]. *)
  partnered : int Tbl.Feature.t;
      (** Per literal key, the postings of [binary] made by [counted] sides. Every other posting is
          of a side whose complement class has no ids, so it has no inverse and rewrites nothing: a
          binary query whose buckets hold no counted posting finds nothing ([candidates]), whatever
          its budget. *)
  mutable touched : klass list;
      (** classes added to, or holding a removed id, since the last [compact] (in [ids] or [sides]);
          every other class's [ids] is still sorted, duplicate-free and made of stored ids *)
  mutable compactions : int;
  mutable unit_deleted : int;
  mutable literal_rewritten : int;
  mutable literal_justified : int;
      (** Rewrites whose retirement is a redundancy deletion: every one under [Redundant]; under
          [Legacy] the ones that also meet the redundancy condition (a diagnostic count). *)
  mutable literal_units : int;  (** Rewrites of a unit target (only under [Legacy]). *)
  mutable literal_derived : int;  (** Consequences offered by {!derive} (only under [Derive]). *)
  mutable trials : int;
  mutable exhausted : int;
  mutable skipped : int;  (** binary queries [candidates] refused (diagnostics) *)
  order : Ordering.order;
  equivalence : equivalence;
}

let create ?(order = Ordering.standard) ?(equivalence = Redundant) () =
  {
    units = Index.create ();
    binary = Index.create ();
    classes = Keys.create 32;
    steps = Tbl.Int.create 64;
    inverse = Tbl.Int.create 64;
    partnered = Tbl.Feature.create 16;
    touched = [];
    compactions = 0;
    unit_deleted = 0;
    literal_rewritten = 0;
    literal_justified = 0;
    literal_units = 0;
    literal_derived = 0;
    trials = 0;
    exhausted = 0;
    skipped = 0;
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

(* The class of [k], made empty if there is none. *)
let klass t k =
  match Keys.find_opt t.classes k with
  | Some c -> c
  | None ->
      let c = { value = k; ids = []; sides = []; mark = -1 } in
      Keys.add t.classes k c;
      c

(* The inverse candidates of a variant key: the stored sides with that key (the [equivalents]
   entry of tests/regression/contraction_reference.ml). *)
let equivalents t k = match Keys.find_opt t.classes k with Some c -> c.ids | None -> []

(* A side's postings enter or leave the [partnered] counts. *)
let count t side =
  side.counted <- true;
  List.iter
    (fun f ->
      Tbl.Feature.replace t.partnered f
        (1 + Option.value ~default:0 (Tbl.Feature.find_opt t.partnered f)))
    side.features

let uncount t side =
  side.counted <- false;
  List.iter
    (fun f ->
      match Tbl.Feature.find_opt t.partnered f with
      | Some n when n > 1 -> Tbl.Feature.replace t.partnered f (n - 1)
      | _ -> Tbl.Feature.remove t.partnered f)
    side.features

(* [c] got its first id (or lost its last): the live sides whose complement class it is gain (or
   lose) their inverse candidates. [c.sides] lists those sides, and ids that no longer have such a
   side, which are passed over. *)
let recount t c ~present =
  List.iter
    (fun id ->
      match Tbl.Int.find_opt t.inverse id with
      | Some side when side.opp == c && side.counted <> present ->
          if present then count t side else uncount t side
      | _ -> ())
    c.sides

let add t (s : step) =
  match s.clause with
  | [ _ ] ->
      Index.add t.units (indexed s);
      Tbl.Int.replace t.steps s.id s
  | [ _; _ ] ->
      Index.add t.binary (indexed s);
      Tbl.Int.replace t.steps s.id s;
      (* A stored id added again replaces its side: the old one leaves the counts (and its
         complement class is cleaned of the repeated id at the next [compact]). *)
      (match Tbl.Int.find_opt t.inverse s.id with
      | Some old ->
          if old.counted then uncount t old;
          t.touched <- old.opp :: t.touched
      | None -> ());
      let own = klass t (key (Variant_index.key s.clause)) in
      let fresh = own.ids = [] in
      own.ids <- s.id :: own.ids;
      t.touched <- own :: t.touched;
      let opposite = complement s.clause in
      let opp = klass t (key (Variant_index.key opposite)) in
      let side =
        {
          opposite;
          opposite_key = opp.value;
          own;
          opp;
          features = List.map Clause.key s.clause;
          counted = false;
          variants = [];
        }
      in
      Tbl.Int.replace t.inverse s.id side;
      if fresh then recount t own ~present:true;
      opp.sides <- s.id :: opp.sides;
      if opp.ids <> [] && not side.counted then count t side
  | _ -> ()

let remove t id =
  Index.remove t.units id;
  Index.remove t.binary id;
  (match Tbl.Int.find_opt t.inverse id with
  | Some side ->
      if side.counted then uncount t side;
      t.touched <- side.own :: side.opp :: t.touched
  | None -> ());
  Tbl.Int.remove t.steps id;
  Tbl.Int.remove t.inverse id

let normalize t ids = List.filter (Tbl.Int.mem t.steps) ids |> List.sort_uniq compare

(* A class's [ids] normalized (the ones that left [steps] dropped, sorted, once each) and its
   [sides] cleaned; a class left with neither leaves the table. *)
let normalize_class t c =
  if c.mark <> t.compactions then (
    c.mark <- t.compactions;
    (match c.ids with
    | [] -> ()
    | ids -> (
        match normalize t ids with
        | [] ->
            c.ids <- [];
            recount t c ~present:false
        | ids -> c.ids <- ids));
    c.sides <-
      List.filter
        (fun id ->
          match Tbl.Int.find_opt t.inverse id with Some side -> side.opp == c | None -> false)
        c.sides
      |> List.sort_uniq Int.compare;
    if c.ids = [] && c.sides = [] then Keys.remove t.classes c.value)

(* Every class normalized: the reference for [compact] in the unit tests. *)
let compact_all t =
  Index.compact_all t.units;
  Index.compact_all t.binary;
  t.touched <- [];
  t.compactions <- t.compactions + 1;
  List.iter (normalize_class t) (Keys.fold (fun _ c cs -> c :: cs) t.classes [])

(* Normalizing an untouched class would give it back unchanged, so only the touched ones are
   normalized. *)
let compact t =
  Index.compact t.units;
  Index.compact t.binary;
  let touched = t.touched in
  t.touched <- [];
  t.compactions <- t.compactions + 1;
  List.iter (normalize_class t) touched

(* Whether a binary query of [clause] can meet a posting of a side with an inverse candidate: a
   query whose buckets (the complements' keys) hold none finds nothing. *)
let candidates t (clause : clause) =
  Tbl.Feature.length t.partnered > 0
  && List.exists (fun l -> Tbl.Feature.mem t.partnered (Intern.flip (Clause.key l))) clause
  ||
  (t.skipped <- t.skipped + 1;
   false)

(* [Variant_index.variants other.clause opposite], remembered per side and stored step. *)
let variant side (other : step) =
  let rec find = function
    | [] ->
        let answer = Variant_index.variants other.clause side.opposite in
        (* A side meets few stored variants of its complement; the list is bounded all the
           same. *)
        if List.compare_length_with side.variants 8 >= 0 then side.variants <- [];
        side.variants <- (other, answer) :: side.variants;
        answer
    | (s, answer) :: rest -> if s == other then answer else find rest
  in
  find side.variants

let rec apply sigma = function
  | V v as x -> Option.value ~default:x (Sym.assoc_opt v sigma)
  | Fn (f, xs) -> Fn (f, List.map (apply sigma) xs)

(* [binary]: also rewrite with binary sides and their inverses (literal rewriting); off, only
   unit deletion. *)
(* [accept]: which binary rewrites the search offers: [`Rule] the ones [t.equivalence] allows
   ([Derive] as [Redundant]); [`Unjustified] only the ones the redundancy condition refuses
   ({!derive}). *)
(* [skip] (the default): a binary query that [candidates] refuses is not run; it would find
   nothing, so the answer is the same, and only the [trials], [exhausted] and [guard] calls it
   would have made are left out. [~skip:false] runs it: the reference of the unit tests. *)
let search ~accept ?(budget = 1024) ?(binary = true) ?(skip = true) ~guard t (target : step) =
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
    | None when skip && not (candidates t target.clause) -> None
    | None ->
        query t.binary (fun j l p ->
            t.trials <- t.trials + 1;
            let side = p.Index.step in
            let found = Tbl.Int.find_opt t.inverse side.id in
            match found with
            | Some cached when skip && not cached.counted ->
                (* Its complement class has no ids: [ids] below would be [], which spends no tick
                   and finds no inverse. *)
                None
            | _ ->
                let opposite, ids =
                  match found with
                  | Some cached -> (cached.opposite, cached.opp.ids)
                  | None ->
                      let stored =
                        match Tbl.Int.find_opt t.steps side.id with Some s -> s | None -> side
                      in
                      let opposite = complement stored.clause in
                      (opposite, equivalents t (key (Variant_index.key opposite)))
                in
                let inverse =
                  ids
                  |> List.find_map (fun id ->
                      tick ();
                      match Tbl.Int.find_opt t.steps id with
                      | Some other
                        when id <> target.id
                             &&
                             match found with
                             | Some cached -> variant cached other
                             | None -> Variant_index.variants other.clause opposite ->
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
                                    rule =
                                      Resolve (side.id, p.literal, target.id, j, into_side sigma);
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

let find ?budget ?binary ?skip ~guard t target =
  search ~accept:`Rule ?budget ?binary ?skip ~guard t target

(** Under [Derive]: the first binary rewrite of [target] that [Legacy] would make and the redundancy
    condition refuses, as a consequence to add while the target stays (its [using] is the side
    clause alone: nothing is retired). [None] under the other rules. With [skip] (the default) a
    target whose binary query [candidates] refuses returns [None] before the query is set up. *)
let derive ?budget ?(skip = true) ~guard t (target : step) =
  if t.equivalence <> Derive then None
  else if skip && not (candidates t target.clause) then None
  else search ~accept:`Unjustified ?budget ~binary:true ~skip:false ~guard t target
