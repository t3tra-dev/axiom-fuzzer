open Wire
(** Independent input reconstruction using Rocq-extracted operations. Internal to Kernel's API; it
    does not reuse search operations. *)

exception Reject of string

let require b message = if not b then raise (Reject message)

module Normalize = Wire_normalizer.WireNormalize (struct
  type function_name = string
  type predicate_name = string

  let leb a b = Stdlib.compare a b <= 0
  let equal a b = a = b
end)

let normalize c =
  match Normalize.normalize max_int c with
  | Some result -> result
  | None -> raise (Reject "kernel variable resource limit")

(* Wire shares the extracted term/atom types. Constructor and variable-support
   laws are proved for these concrete types; both extracted CNF wrappers return
   Wire clauses directly. Normalization is extracted as well, and Verified.check
   checks the input encoding before the numeric refutation checker runs.
   Source.Kernel rechecks the complete preprocessing and authority at final
   acceptance. Search is independent; the proposed circuit is only a hint. *)
module Checked = Source_checker

let prepare_input ?(guard = fun () -> ()) ?(mode = Hybrid) (ax : axiom) =
  let support atom =
    guard ();
    match Checked.checked_wire_support atom with
    | Some vars -> vars
    | None -> raise (Reject "invalid base matrix atom or variable")
  in
  let clauses m =
    match
      Checked.wire_distributive_cnf
        (fun () ->
          guard ();
          true)
        100000 m
    with
    | Some cs -> (cs, Kernel_checker.DistributiveEvidence)
    | None -> raise (Reject "kernel CNF resource limit")
  in
  let normal = Wire.checked_source ~guard ax.formula |> Checked.nnf true in
  let quantified =
    Checked.wire_quantifiers
      (fun () ->
        guard ();
        true)
      max_int ax.axiom_id normal
  in
  let m =
    match quantified with
    | None -> raise (Reject "invalid or oversized quantifier traversal")
    | Some r -> (
        match
          Checked.wire_checked_universals
            (fun () ->
              guard ();
              true)
            max_int r.supplied_value
        with
        | Some m -> m
        | None -> raise (Reject "invalid universal variable scope"))
  in
  let threshold = hybrid_cnf_limit in
  let rec size = function
    | Checked.MLiteral _ -> 1
    | MConj ms -> List.map size ms |> List.fold_left (fun a b -> min (threshold + 1) (a + b)) 0
    | MDisj ms -> List.map size ms |> List.fold_left (fun a b -> min (threshold + 1) (a * b)) 1
  in
  let definitions () =
    let fresh = ref 0 and declarations = ref [] and remaining = ref 99999 in
    let rec introduce m =
      guard ();
      match m with
      | Checked.MLiteral (positive, atom) -> Checked.DBase (positive, atom)
      | MConj ms -> connective true ms
      | MDisj ms -> connective false ms
    and connective conjunction ms =
      let args = List.map introduce ms in
      let width = List.length args in
      require (width < !remaining) "kernel CNF resource limit";
      remaining := !remaining - width - 1;
      let id = !fresh in
      incr fresh;
      let arguments = Checked.definition_variables support args in
      declarations := { Checked.conjunction; arguments; children = args } :: !declarations;
      Checked.DAux (true, id, arguments)
    in
    let root = introduce m in
    (* Freeze the proposed circuit before handing its read-only lookup to the
       extracted checker. Rejecting/raising callbacks cannot accept partial CNF. *)
    let declarations = Array.of_list (List.rev !declarations) in
    let lookup id =
      guard ();
      if id >= 0 && id < Array.length declarations then Some declarations.(id) else None
    in
    let equal a b =
      guard ();
      a = b
    in
    match
      Checked.wire_definitional_cnf lookup
        (fun () ->
          guard ();
          true)
        equal (Array.length declarations) 100000 ax.axiom_id m root
    with
    | Some cs -> (cs, Kernel_checker.DefinitionalEvidence (Array.to_list declarations, root))
    | None -> raise (Reject "invalid or oversized definition circuit")
  in
  let cs, cnf_hint =
    match mode with
    | Distributive -> clauses m
    | Hybrid when size m <= threshold -> clauses m
    | Hybrid | Definitional -> definitions ()
  in
  ({ Kernel_checker.original_axiom = ax; cnf_hint }, List.map normalize cs)

let input_clauses ?guard ?mode ax = snd (prepare_input ?guard ?mode ax)
