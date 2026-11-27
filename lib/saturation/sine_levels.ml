open Wire
(** SInE trigger levels of the input axioms, measured from the negated-conjecture axioms (Hoder and
    Voronkov, CADE 2011), as clause-selection guidance only. No axiom is ever removed or delayed
    outside the clause queues, so the search space and completeness are those of the base strategy;
    only the selection order changes. Levels are a search hint: they never reach a certificate.

    A symbol is a (head, arity) key of a function or predicate symbol (equality is not a symbol).
    [occ s] is the number of axioms whose clauses contain [s]. A non-goal axiom [A] is triggered by
    a symbol [s] of [A] when [occ s <= generality] or [occ s <= tolerance * min occ] over the
    symbols of [A]. Level 0: the negated-conjecture axioms and their symbols. An axiom triggered by
    a symbol of level [k] that has no level yet gets level [k + 1], and so do its symbols that have
    none yet. Axioms that are never reached get [unreached]: the reached axioms are exactly the ones
    SInE with these parameters would select, here the goal-near layer of a layered selection
    ([Evaluation.Below_level] with the cutoff [reachable]) instead of a filter.

    The parameters were fixed before any measurement (a tolerance of about 3-5 and a generality
    threshold of about 8), not fitted on any corpus. *)

type params = { tolerance : float; generality : int }

let default = { tolerance = 3.0; generality = 8 }

type t = { axiom_level : (int, int) Hashtbl.t  (** Axiom id -> level of the reached axioms. *) }

(** The level of an axiom that the trigger relation never reaches, and of an axiom added after the
    initial ones. *)
let unreached = 1_000_000

(** The cutoff of the layer of the reached axioms and of every clause with a reached ancestor. *)
let reachable = unreached - 1

(* The distinct symbol keys of a clause list, in first-occurrence order. *)
let symbols (clauses : clause list) =
  let seen = Hashtbl.create 16 and order = ref [] in
  let add key =
    if not (Hashtbl.mem seen key) then (
      Hashtbl.add seen key ();
      order := key :: !order)
  in
  let rec term = function
    | V _ -> ()
    | Fn (f, ts) ->
        add (Ordering.Function f, List.length ts);
        List.iter term ts
  in
  List.iter
    (List.iter (fun l ->
         match l.atom with
         | E (s, t) ->
             term s;
             term t
         | P (p, ts) ->
             add (Ordering.Predicate p, List.length ts);
             List.iter term ts
         | D (d, ts) ->
             add (Ordering.Definition d, List.length ts);
             List.iter term ts))
    clauses;
  List.rev !order

(** The levels of [axioms], each given as (axiom id, its clauses, whether it is a negated
    conjecture). [None] without a negated-conjecture axiom: then there is nothing to measure from.
*)
let compute ?(params = default) (axioms : (int * clause list * bool) list) =
  if not (List.exists (fun (_, _, goal) -> goal) axioms) then None
  else
    let axioms = List.map (fun (id, clauses, goal) -> (id, symbols clauses, goal)) axioms in
    let occ = Hashtbl.create 256 in
    List.iter
      (fun (_, syms, _) ->
        List.iter
          (fun s -> Hashtbl.replace occ s (1 + Option.value ~default:0 (Hashtbl.find_opt occ s)))
          syms)
      axioms;
    let occ s = Option.value ~default:0 (Hashtbl.find_opt occ s) in
    (* The trigger relation: symbol -> the non-goal axioms it triggers, in input order. *)
    let triggers = Hashtbl.create 256 in
    List.iter
      (fun ((_, syms, goal) as axiom) ->
        if (not goal) && syms <> [] then
          let least = List.fold_left (fun m s -> min m (occ s)) max_int syms in
          List.iter
            (fun s ->
              let n = occ s in
              if n <= params.generality || float_of_int n <= params.tolerance *. float_of_int least
              then
                Hashtbl.replace triggers s
                  (axiom :: Option.value ~default:[] (Hashtbl.find_opt triggers s)))
            syms)
      axioms;
    let axiom_level = Hashtbl.create 256 and symbol_level = Hashtbl.create 256 in
    let reach level syms =
      List.filter
        (fun s ->
          if Hashtbl.mem symbol_level s then false
          else (
            Hashtbl.add symbol_level s level;
            true))
        syms
    in
    let frontier =
      List.concat_map
        (fun (id, syms, goal) ->
          if goal then (
            Hashtbl.replace axiom_level id 0;
            reach 0 syms)
          else [])
        axioms
    in
    let rec spread level frontier =
      if frontier <> [] then
        let next =
          List.concat_map
            (fun s ->
              List.concat_map
                (fun (id, syms, _) ->
                  if Hashtbl.mem axiom_level id then []
                  else (
                    Hashtbl.add axiom_level id (level + 1);
                    reach (level + 1) syms))
                (List.rev (Option.value ~default:[] (Hashtbl.find_opt triggers s))))
            frontier
        in
        spread (level + 1) next
    in
    spread 0 frontier;
    (* An axiom without symbols (only equations between variables) is triggered by nothing; it is
       relevant to every problem, so it joins the first ring. *)
    List.iter
      (fun (id, syms, _) ->
        if syms = [] && not (Hashtbl.mem axiom_level id) then Hashtbl.replace axiom_level id 1)
      axioms;
    Some { axiom_level }

let level t axiom_id = Option.value ~default:unreached (Hashtbl.find_opt t.axiom_level axiom_id)
