open Wire

let candidates a clauses =
  let convert l =
    let names = Hashtbl.create 8 in
    let rec term = function
      | V v ->
          let i =
            match Hashtbl.find_opt names v with
            | Some i -> i
            | None ->
                let i = Hashtbl.length names in
                Hashtbl.add names v i;
                i
          in
          Source.free a i
      | Fn (Original s, ts) -> Source.apply a s (List.map term ts)
      | Fn (Skolem _, _) -> raise Exit
    in
    try
      let f =
        match l.atom with
        | P (p, ts) -> Source.pred a p (List.map term ts)
        | E (x, y) -> Source.eq a (term x) (term y)
        | D _ -> raise Exit
      in
      [ f; Source.not_ a f ]
    with Exit -> []
  in
  clauses
  |> List.concat_map (fun (s : step) -> List.concat_map convert s.clause)
  |> List.sort_uniq compare

(* Incremental, bounded heuristic synthesis. [candidates] above remains a
   full-scan atomic oracle for differential tests and measurements. *)
type config = {
  compounds : bool;
  ranked : bool;
  constraints : bool;
  match_limit : int;
  match_steps : int;
  max_size : int;
  max_variables : int;
  literal_limit : int;
  term_limit : int;
  candidates_per_clause : int;
  capacity : int;
  clauses_per_cycle : int;
  proposals_per_cycle : int;
}

let default_config =
  {
    compounds = true;
    ranked = true;
    constraints = true;
    match_limit = 32;
    match_steps = 4096;
    max_size = 5;
    max_variables = 4;
    literal_limit = 8;
    term_limit = 32;
    candidates_per_clause = 64;
    capacity = 256;
    clauses_per_cycle = 8;
    proposals_per_cycle = 8;
  }

type metrics = {
  mutable observed : int;
  mutable processed : int;
  mutable stale : int;
  mutable literals : int;
  mutable rejected_literals : int;
  mutable candidates : int;
  mutable unique : int;
  mutable duplicates : int;
  mutable filtered : int;
  mutable dropped : int;
  mutable dropped_events : int;
  mutable offered : int;
  mutable already_injected : int;
  mutable peak_pending : int;
  mutable matches : int;
  mutable complementary : int;
  mutable constrained : int;
  mutable history_patterns : int;
  mutable history_offered : int;
  mutable replaced : int;
  mutable exhausted_matches : int;
  mutable demands : int;
  mutable demanded_offered : int;
}

let empty_metrics () =
  {
    observed = 0;
    processed = 0;
    stale = 0;
    literals = 0;
    rejected_literals = 0;
    candidates = 0;
    unique = 0;
    duplicates = 0;
    filtered = 0;
    dropped = 0;
    dropped_events = 0;
    offered = 0;
    already_injected = 0;
    peak_pending = 0;
    matches = 0;
    complementary = 0;
    constrained = 0;
    history_patterns = 0;
    history_offered = 0;
    replaced = 0;
    exhausted_matches = 0;
    demands = 0;
    demanded_offered = 0;
  }

type proposal = {
  formula : Source.formula;
  size : int;
  mutable history : int;
  mutable demanded : bool;
  mutable complementary : bool;
  mutable constrained : bool;
  mutable offered : bool;
  mutable queued : bool;
}

type t = {
  arena : Source.t;
  config : config;
  metrics : metrics;
  events : step Queue.t;
  pending : proposal Queue.t;
  seen_steps : (int, unit) Hashtbl.t;
  seen : (Source.formula, proposal) Hashtbl.t;
  mutable recent : (int * clause) list;
}

let create ?(config = default_config) arena =
  if
    config.max_size < 1 || config.max_variables < 0 || config.literal_limit < 1
    || config.term_limit < 1 || config.candidates_per_clause < 1 || config.capacity < 1
    || config.clauses_per_cycle < 1 || config.proposals_per_cycle < 1 || config.match_limit < 1
    || config.match_steps < 1
  then invalid_arg "invalid guided synthesis budget";
  {
    arena;
    config;
    metrics = empty_metrics ();
    events = Queue.create ();
    pending = Queue.create ();
    seen_steps = Hashtbl.create 128;
    seen = Hashtbl.create 256;
    recent = [];
  }

let observe t (step : step) =
  if not (Hashtbl.mem t.seen_steps step.id) then (
    Hashtbl.add t.seen_steps step.id ();
    t.metrics.observed <- t.metrics.observed + 1;
    if Queue.length t.events >= t.config.capacity then (
      ignore (Queue.take t.events);
      t.metrics.dropped_events <- t.metrics.dropped_events + 1);
    Queue.add step t.events)

let has_work t = not (Queue.is_empty t.events && Queue.is_empty t.pending)

let collect t is_live =
  let events = Queue.fold (fun xs (s : step) -> if is_live s.id then s :: xs else xs) [] t.events in
  Queue.clear t.events;
  List.iter (fun s -> Queue.add s t.events) (List.rev events);
  t.recent <- List.filter (fun (id, _) -> is_live id) t.recent;
  Hashtbl.filter_map_inplace (fun id () -> if is_live id then Some () else None) t.seen_steps;
  Hashtbl.filter_map_inplace (fun _ p -> if p.queued then Some p else None) t.seen

let priority p = (p.demanded, p.history, p.constrained, p.complementary, -p.size)

let remove_pending t selected =
  let keep = Queue.create () in
  Queue.iter (fun p -> if p != selected then Queue.add p keep) t.pending;
  Queue.clear t.pending;
  Queue.transfer keep t.pending;
  selected.queued <- false

let admit ?(demanded = false) ?(history = 0) ?(complementary = false) ?(constrained = false) t
    ~guard f =
  guard ();
  t.metrics.candidates <- t.metrics.candidates + 1;
  if
    Source.size t.arena f > t.config.max_size
    || List.length (Source.free_vars t.arena f) > t.config.max_variables
  then t.metrics.filtered <- t.metrics.filtered + 1
  else
    let proposal =
      match Hashtbl.find_opt t.seen f with
      | Some p ->
          t.metrics.duplicates <- t.metrics.duplicates + 1;
          p.history <- max p.history history;
          p.demanded <- p.demanded || demanded;
          p.complementary <- p.complementary || complementary;
          p.constrained <- p.constrained || constrained;
          p
      | None ->
          let p =
            {
              formula = f;
              size = Source.size t.arena f;
              history;
              demanded;
              complementary;
              constrained;
              offered = false;
              queued = false;
            }
          in
          Hashtbl.add t.seen f p;
          t.metrics.unique <- t.metrics.unique + 1;
          p
    in
    if (not proposal.offered) && not proposal.queued then (
      if Queue.length t.pending >= t.config.capacity && t.config.ranked then (
        let worst = ref (Queue.peek t.pending) in
        Queue.iter (fun p -> if priority p < priority !worst then worst := p) t.pending;
        if priority proposal > priority !worst then (
          remove_pending t !worst;
          t.metrics.replaced <- t.metrics.replaced + 1));
      if Queue.length t.pending >= t.config.capacity then t.metrics.dropped <- t.metrics.dropped + 1
      else (
        proposal.queued <- true;
        Queue.add proposal t.pending;
        t.metrics.peak_pending <- max t.metrics.peak_pending (Queue.length t.pending)))

let source_only ~limit literal =
  let left = ref limit in
  let rec term t =
    decr left;
    if !left < 0 then raise Exit;
    match t with
    | V _ -> ()
    | Fn (Original _, ts) -> List.iter term ts
    | Fn (Skolem _, _) -> raise Exit
  in
  try
    (match literal.atom with D _ -> raise Exit | atom -> List.iter term (Clause.atom_terms atom));
    true
  with Exit -> false

let source_atom arena names literal =
  let rec term = function
    | V v ->
        let i =
          match Hashtbl.find_opt names v with
          | Some i -> i
          | None ->
              let i = Hashtbl.length names in
              Hashtbl.add names v i;
              i
        in
        Source.free arena i
    | Fn (Original s, ts) -> Source.apply arena s (List.map term ts)
    | Fn (Skolem _, _) -> invalid_arg "guided synthesis received a Skolem term"
  in
  match literal.atom with
  | P (p, ts) -> Source.pred arena p (List.map term ts)
  | E (x, y) -> Source.eq arena (term x) (term y)
  | D _ -> invalid_arg "guided synthesis received an auxiliary predicate"

let rec first n = function [] -> [] | _ when n = 0 -> [] | x :: xs -> x :: first (n - 1) xs

let signed_formula arena names l =
  let f = source_atom arena names l in
  if l.positive then f else Source.not_ arena f

(* A wanted consequence only ranks legal schema arguments. Never turn it into
   a premise, and never expose auxiliary/Skolem symbols to the Source language. *)
let request ?(guard = fun () -> ()) t clause =
  if
    clause <> []
    && List.length clause <= t.config.literal_limit
    && List.for_all (source_only ~limit:t.config.term_limit) clause
  then (
    let names = Hashtbl.create 8 in
    let formula = Source.and_ t.arena (List.map (signed_formula t.arena names) clause) in
    t.metrics.demands <- t.metrics.demands + 1;
    admit ~demanded:true ~constrained:true t ~guard formula)

exception Match_exhausted

let synthesize t ~guard (step : step) =
  let remaining = ref t.config.candidates_per_clause in
  let offer ?(complementary = false) ?(constrained = false) f =
    if !remaining > 0 then (
      decr remaining;
      if constrained then t.metrics.constrained <- t.metrics.constrained + 1;
      admit ~complementary ~constrained t ~guard f)
  in
  let both f =
    offer f;
    offer (Source.not_ t.arena f)
  in
  let literals =
    first t.config.literal_limit step.clause
    |> List.filter (fun l ->
        guard ();
        t.metrics.literals <- t.metrics.literals + 1;
        if source_only ~limit:t.config.term_limit l then true
        else (
          t.metrics.rejected_literals <- t.metrics.rejected_literals + 1;
          false))
  in
  List.iter (fun l -> both (source_atom t.arena (Hashtbl.create 8) l)) literals;
  (if t.config.ranked || t.config.constraints then
     let matches = ref t.config.match_limit in
     let left = Clause.scope 1 literals in
     List.iter
       (fun (_, clause) ->
         if !matches > 0 then
           let right = Clause.scope 2 clause in
           List.iteri
             (fun i l ->
               List.iteri
                 (fun j r ->
                   guard ();
                   if !matches > 0 && l.positive <> r.positive then
                     List.iter
                       (fun equations ->
                         if !matches > 0 then (
                           decr matches;
                           t.metrics.matches <- t.metrics.matches + 1;
                           (* A short-lived arena bounds matching storage. The
                             search engine's mutable unifier is never borrowed. *)
                           let work = ref t.config.match_steps in
                           let check_match () =
                             guard ();
                             decr work;
                             if !work < 0 then raise Match_exhausted
                           in
                           try
                             Unify.solve
                               (Unify.create ~guard:check_match (Term.create ()))
                               equations
                               (fun _ apply ->
                                 t.metrics.complementary <- t.metrics.complementary + 1;
                                 List.iter
                                   (fun l ->
                                     let f = source_atom t.arena (Hashtbl.create 8) l in
                                     offer ~complementary:true f;
                                     offer ~complementary:true (Source.not_ t.arena f))
                                   [ l; r ];
                                 if t.config.constraints && !remaining > 0 then
                                   let residual =
                                     Clause.remove i left @ Clause.remove j right
                                     |> List.map (Clause.map_literal apply)
                                   in
                                   let pivot = Clause.map_literal apply l in
                                   (* Recheck term bounds after instantiation: two
                                   small patterns may unify to a much larger one. *)
                                   if
                                     List.for_all
                                       (source_only ~limit:t.config.term_limit)
                                       (pivot :: residual)
                                   then (
                                     let f = source_atom t.arena (Hashtbl.create 8) pivot in
                                     offer ~constrained:true f;
                                     offer ~constrained:true (Source.not_ t.arena f);
                                     let names = Hashtbl.create 8 in
                                     let rest =
                                       Source.or_ t.arena
                                         (List.map (signed_formula t.arena names) residual)
                                     in
                                     offer ~constrained:true (Source.not_ t.arena rest);
                                     offer ~constrained:true rest))
                           with Match_exhausted ->
                             t.metrics.exhausted_matches <- t.metrics.exhausted_matches + 1))
                       (Calculus.equations l.atom r.atom))
                 right)
             left)
       t.recent);
  t.recent <- first t.config.capacity ((step.id, literals) :: t.recent);
  if t.config.compounds && !remaining > 0 then (
    (* A single variable map across a clause is essential: converting every
       literal separately would identify unrelated variables in compounds. *)
    let names = Hashtbl.create 8 in
    let signed =
      List.map
        (fun l ->
          let f = source_atom t.arena names l in
          if l.positive then f else Source.not_ t.arena f)
        literals
    in
    let enrich f =
      if !remaining > 0 then (
        both f;
        (* Preserve Free 0 as the principal schema variable; bind the final
           other parameter to form small quantified conditions. *)
        match List.rev (Source.free_vars t.arena f) with
        | v :: _ when v > 0 ->
            offer (Source.all t.arena [ v ] f);
            offer (Source.ex t.arena [ v ] f)
        | _ -> ())
    in
    List.iter enrich signed;
    let rec pairs = function
      | [] -> ()
      | f :: rest ->
          List.iter
            (fun g ->
              if !remaining > 0 then (
                enrich (Source.and_ t.arena [ f; g ]);
                enrich (Source.or_ t.arena [ f; g ])))
            rest;
          if !remaining > 0 then pairs rest
    in
    pairs signed)

let pump ?(guard = fun () -> ()) ?(is_live = fun _ -> true) t =
  t.recent <-
    List.filter
      (fun (id, _) ->
        guard ();
        is_live id)
      t.recent;
  let remaining = ref t.config.clauses_per_cycle in
  while !remaining > 0 && not (Queue.is_empty t.events) do
    guard ();
    decr remaining;
    let step = Queue.take t.events in
    if not (is_live step.id) then t.metrics.stale <- t.metrics.stale + 1
    else (
      t.metrics.processed <- t.metrics.processed + 1;
      synthesize t ~guard step)
  done

(* A conflict is evidence for a proposal, not a new Source axiom. Replace each
   Skolem application by a fresh parameter, retaining repeated-term sharing.
   This deliberately generalizes a pattern; Theory still authorizes every
   instantiated axiom independently. *)
let feedback ?(guard = fun () -> ()) t steps =
  let names = Hashtbl.create 16 in
  let remaining = ref t.config.term_limit in
  let rec abstract term =
    guard ();
    decr remaining;
    if !remaining < 0 then raise Match_exhausted;
    match term with
    | Fn (Skolem _, _) as term ->
        let id =
          match Hashtbl.find_opt names term with
          | Some id -> id
          | None ->
              let id = Hashtbl.length names in
              Hashtbl.add names term id;
              id
        in
        V (3, id)
    | Fn (symbol, args) -> Fn (symbol, List.map abstract args)
    | V _ as term -> term
  in
  List.iter
    (fun (step : step) ->
      guard ();
      let step =
        {
          step with
          clause =
            List.filter_map
              (fun literal ->
                remaining := t.config.term_limit;
                try Some (Clause.map_literal abstract literal) with Match_exhausted -> None)
              (first t.config.literal_limit step.clause);
        }
      in
      synthesize t ~guard step;
      List.iter
        (fun f -> admit ~history:1 ~constrained:true t ~guard f)
        (candidates t.arena [ step ]))
    (first 8 steps)

let take ?(guard = fun () -> ()) ?(eligible = fun _ -> true) t =
  let rec next () =
    guard ();
    if Queue.is_empty t.pending then None
    else
      let proposal =
        if not t.config.ranked then Queue.take t.pending
        else
          let best = ref (Queue.peek t.pending) in
          Queue.iter
            (fun p ->
              guard ();
              if priority p > priority !best then best := p)
            t.pending;
          remove_pending t !best;
          !best
      in
      proposal.queued <- false;
      proposal.offered <- true;
      let f = proposal.formula in
      if eligible f then (
        t.metrics.offered <- t.metrics.offered + 1;
        if proposal.demanded then t.metrics.demanded_offered <- t.metrics.demanded_offered + 1;
        if proposal.history > 0 then t.metrics.history_offered <- t.metrics.history_offered + 1;
        Some f)
      else (
        t.metrics.already_injected <- t.metrics.already_injected + 1;
        next ())
  in
  next ()

(* History contains portable Source patterns, never executable code or arena
   IDs. A proof contributes each pattern once, so long proofs do not swamp the
   frequency signal. Patterns remain proposals, not additional axioms. *)
let learn theory certificate =
  (match Kernel.check theory certificate with
  | Ok _ -> ()
  | Error e -> invalid_arg ("guided proof history: " ^ e));
  let certificate = Proof.prune certificate in
  let patterns = ref [] in
  let add f = patterns := f :: !patterns in
  let rec atoms = function
    | (Pred _ | Eq _) as f ->
        let names = Hashtbl.create 8 in
        let rec term = function
          | (B _ | F _) as v ->
              let i =
                match Hashtbl.find_opt names v with
                | Some i -> i
                | None ->
                    let i = Hashtbl.length names in
                    Hashtbl.add names v i;
                    i
              in
              F i
          | App (s, ts) -> App (s, List.map term ts)
        in
        let f =
          match f with
          | Pred (s, ts) -> Pred (s, List.map term ts)
          | Eq (x, y) ->
              let x = term x in
              Eq (x, term y)
          | _ -> assert false
        in
        add f;
        add (Neg f)
    | Neg f | All f | Ex f -> atoms f
    | Conj fs | Disj fs -> List.iter atoms fs
    | Top | Bot -> ()
  in
  (match certificate.natural with
  | None ->
      List.iter
        (fun (a : axiom) ->
          match a.origin with Instance (_, phi) -> add phi | _ -> atoms a.formula)
        certificate.axioms
  | Some code ->
      let module N = Natural_checker in
      let rec permission p =
        match p with
        | N.SchemaPermission (_, _, _, phi) -> add phi
        | EquivalentPermission (p, _) -> permission p
        | _ -> Option.iter atoms (N.authorize (Theory.manifest theory) p)
      in
      let c = Option.get (N.certificate_value code) in
      List.iter
        (function
          | Wire_types.Pair (Number 0, p) -> Option.iter permission (N.permission_value p) | _ -> ())
        c.assumptions);
  List.sort_uniq compare !patterns

let seed ?(guard = fun () -> ()) t history =
  let frequencies = Hashtbl.create 64 in
  List.iter
    (fun f ->
      guard ();
      (* Bound before arena allocation, including nested term nodes. *)
      let remaining =
        ref
          (if t.config.term_limit > max_int / t.config.max_size then max_int
           else t.config.term_limit * t.config.max_size)
      in
      let visit () =
        decr remaining;
        if !remaining < 0 then raise Exit
      in
      let rec term = function
        | B _ | F _ -> visit ()
        | App (_, ts) ->
            visit ();
            List.iter term ts
      in
      let rec formula = function
        | Top | Bot -> visit ()
        | Pred (_, ts) ->
            visit ();
            List.iter term ts
        | Eq (x, y) ->
            visit ();
            term x;
            term y
        | Neg f | All f | Ex f ->
            visit ();
            formula f
        | Conj fs | Disj fs ->
            visit ();
            List.iter formula fs
      in
      try
        formula f;
        if Wire.source_scoped f then
          let phi = Wire.import t.arena f in
          if
            Source.size t.arena phi <= t.config.max_size
            && List.length (Source.free_vars t.arena phi) <= t.config.max_variables
          then
            let old = Option.value ~default:0 (Hashtbl.find_opt frequencies phi) in
            Hashtbl.replace frequencies phi (min 1000000 (old + 1))
      with Exit | Invalid_argument _ -> ())
    history;
  Hashtbl.fold (fun f n xs -> (f, n) :: xs) frequencies []
  |> List.sort (fun (f, n) (g, m) ->
      let c = compare m n in
      if c <> 0 then c else compare f g)
  |> first t.config.capacity
  |> List.iter (fun (f, count) ->
      t.metrics.history_patterns <- t.metrics.history_patterns + 1;
      admit ~history:count t ~guard f)
