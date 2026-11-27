(* Reproduction only: a one-off measurement behind a design decision, not run
   by `make release` or any test. Cost of one term comparison (Ordering.greater) in KBO and in LPO
   on the same term pairs. Each
   problem's pairs are the sides of its equations and every pair of its distinct subterms (up to
   [--pairs]); a ported E heuristic gives each ordering its instance for the problem (KBO: e208's,
   LPO: h047b31's). Random pairs use the property tests' signature. CPU time per comparison, the
   median of [--runs] timed rounds of at least [--seconds] each. *)
open Axiom_fuzzer
open Wire

let runs = ref 5
and seconds = ref 0.3
and max_pairs = ref 4000
and problems = ref []

let rec subterms acc t =
  let acc = t :: acc in
  match t with V _ -> acc | Fn (_, ts) -> List.fold_left subterms acc ts

let median xs =
  let a = Array.of_list (List.sort compare xs) in
  a.(Array.length a / 2)

(* CPU nanoseconds per comparison of [pairs] under [order]; also the number of ordered pairs. *)
let measure order pairs =
  let pairs = Array.of_list pairs in
  let n = Array.length pairs in
  let ordered =
    Array.fold_left
      (fun k (s, t) ->
        if Ordering.greater ~order s t || Ordering.greater ~order t s then k + 1 else k)
      0 pairs
  in
  let round () =
    let start = Sys.time () and calls = ref 0 and sink = ref 0 in
    while Sys.time () -. start < !seconds do
      for i = 0 to n - 1 do
        let s, t = pairs.(i) in
        if Ordering.greater ~order s t then incr sink
      done;
      calls := !calls + n
    done;
    ignore (Sys.opaque_identity !sink);
    (Sys.time () -. start) *. 1e9 /. float_of_int !calls
  in
  ignore (round ());
  (median (List.init !runs (fun _ -> round ())), ordered)

let report label clauses pairs =
  let instance name =
    let order = Ordering.create () in
    ignore (Eorder.install (Heuristic.find name).order order clauses);
    order
  in
  let kbo, kbo_ordered = measure (instance "e208") pairs
  and lpo, lpo_ordered = measure (instance "h047b31") pairs in
  Printf.printf "%s,%d,%.1f,%.1f,%.2f,%d,%d\n%!" label (List.length pairs) kbo lpo (lpo /. kbo)
    kbo_ordered lpo_ordered

let () =
  Arg.parse
    [
      ("--runs", Arg.Set_int runs, "N Timed rounds (median)");
      ("--seconds", Arg.Set_float seconds, "S Minimum CPU seconds per round");
      ("--pairs", Arg.Set_int max_pairs, "N Subterm pairs per problem");
    ]
    (fun file -> problems := !problems @ [ file ])
    "ordering_bench [--runs N] [--seconds S] [--pairs N] PROBLEM.p ...";
  print_endline "workload,pairs,kbo_ns,lpo_ns,lpo_over_kbo,kbo_ordered,lpo_ordered";
  List.iter
    (fun file ->
      let text = In_channel.with_open_bin file In_channel.input_all in
      let clauses = List.concat_map (Clausify.run ~mode:Hybrid) (Theory.fixed (Tptp.parse text)) in
      let terms =
        List.concat_map
          (List.concat_map (fun l -> List.concat_map (subterms []) (Clause.atom_terms l.atom)))
          clauses
        |> List.sort_uniq compare |> Array.of_list
      in
      let rng = Random.State.make [| 7 |] in
      let n = Array.length terms in
      let pairs =
        if n < 2 then []
        else
          List.init !max_pairs (fun _ ->
              (terms.(Random.State.int rng n), terms.(Random.State.int rng n)))
      in
      report (Filename.basename file) clauses pairs)
    !problems;
  let rng = Random.State.make [| 20261115 |] in
  let symbols = [| ("f", 1); ("g", 1); ("h", 2); ("k", 3); ("a", 0); ("b", 0); ("c", 0) |] in
  let rec term depth =
    if depth = 0 || Random.State.int rng 4 = 0 then
      if Random.State.int rng 3 = 0 then V (0, Random.State.int rng 3)
      else Fn (Original (fst symbols.(4 + Random.State.int rng 3)), [])
    else
      let name, arity = symbols.(Random.State.int rng 4) in
      Fn (Original name, List.init arity (fun _ -> term (depth - 1)))
  in
  List.iter
    (fun depth ->
      let pairs = List.init 2000 (fun _ -> (term depth, term depth)) in
      let clauses = List.map (fun (s, t) -> [ { positive = true; atom = E (s, t) } ]) pairs in
      report (Printf.sprintf "random-depth%d" depth) clauses pairs)
    [ 3; 5; 7 ]
