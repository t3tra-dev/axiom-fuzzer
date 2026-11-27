open Wire

(* A single production policy: ordinary work requests private Goal recipes,
   accepted-result feedback is disabled, and producer scheduling is separate.
   Keep the historical observation label for comparable saved CSV records. *)
let name = "isolated_requested"

type ids = unit Tbl.Int.t
type source = Publication | Empty

type observations = {
  mutable publication_commits : int;
  mutable empty_commits : int;
  mutable use_calls : int;
  mutable use_applied : int;
  mutable demand_calls : int;
  mutable demand_applied : int;
  publication_ancestors : ids;
  publication_results : ids;
  publication_accepted : ids;
  empty_ancestors : ids;
  empty_results : ids;
  empty_accepted : ids;
}

let create () =
  {
    publication_commits = 0;
    empty_commits = 0;
    use_calls = 0;
    use_applied = 0;
    demand_calls = 0;
    demand_applied = 0;
    publication_ancestors = Tbl.Int.create 32;
    publication_results = Tbl.Int.create 16;
    publication_accepted = Tbl.Int.create 16;
    empty_ancestors = Tbl.Int.create 32;
    empty_results = Tbl.Int.create 8;
    empty_accepted = Tbl.Int.create 8;
  }

let add ids (step : step) =
  if step.id < 0 then invalid_arg "Transfer_policy: virtual ID in ordinary observation";
  Tbl.Int.replace ids step.id ()

let commit t = function
  | Publication -> t.publication_commits <- t.publication_commits + 1
  | Empty -> t.empty_commits <- t.empty_commits + 1

let ancestor t source =
  add (match source with Publication -> t.publication_ancestors | Empty -> t.empty_ancestors)

let result t source =
  add (match source with Publication -> t.publication_results | Empty -> t.empty_results)

let accepted t source _kind =
  add (match source with Publication -> t.publication_accepted | Empty -> t.empty_accepted)

let ids set = Tbl.Int.to_seq_keys set |> List.of_seq |> List.sort compare

(* A dynamic emit scope does not pin a proof node. It marks the direct emitted
   result and synchronous proof descendants only; recording is not admission. *)
type observer = {
  marked : ids;
  mutable first : bool;
  recorded : step -> unit;
  accepted : Goal_transfer.acceptance -> step -> unit;
}

let observer ~recorded ~accepted = { marked = Tbl.Int.create 16; first = true; recorded; accepted }

let derived ?(direct = false) observer (step : step) =
  Option.iter
    (fun t ->
      if direct && t.first then (
        t.first <- false;
        add t.marked step;
        t.recorded step)
      else if List.exists (Tbl.Int.mem t.marked) (Wire.parents step.rule) then add t.marked step)
    observer

let admitted observer kind step =
  Option.iter (fun t -> if Tbl.Int.mem t.marked step.id then t.accepted kind step) observer
