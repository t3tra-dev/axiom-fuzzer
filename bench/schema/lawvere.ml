(* The Lawvere-style diagonal prior: an experimental condition stream for the
   schema benchmark only. It used to be the third sub-lane of the default
   probe lane (lib/synthesis/semantic.ml); it was moved here because it is a
   problem-specific prior (its first condition is the Russell condition
   ~(x in x), and its counterfactual wins were the Russell/Cantor shapes it was
   built for), while the default lane explores broadly with general
   mechanisms only. The library knows no such prior: the bench hands this
   stream to the lane through the generic [Probe_lane.config.prior] hook
   (presets pool-diag and fixed-diag), and axiom-fuzz never sets that hook.

   Nothing here is trusted: a diagonal condition is merely a schema parameter,
   and every resulting proof is still checked by the ordinary kernel. *)

open Axiom_fuzzer

(* Binary relations between two terms [u] and [v] definable by one atom of the
   signature (the base of the diagonal paths). For every binary predicate p:
   p(u,v), p(v,u); per unary function f: p(u,f(v)), p(f(u),v); per binary
   function h (when [binary]): p(u,h(u,v)), p(h(u,v),v). With [equality], per
   unary f: f(u)=v, u=f(v), and per binary h (when [binary]): h(u,v)=v. *)
let base_relations ~equality ~binary signature =
  let functions k = List.filter (fun (_, a) -> a = k) (Signature.functions signature) in
  let unary = functions 1 and binary_fns = if binary then functions 2 else [] in
  let preds = List.filter (fun (_, k) -> k = 2) (Signature.predicates signature) in
  let app f ts = Wire.App (f, ts) in
  List.concat_map
    (fun (p, _) ->
      let pred s t = Wire.Pred (p, [ s; t ]) in
      [ (fun u v -> pred u v); (fun u v -> pred v u) ]
      @ List.concat_map
          (fun (f, _) -> [ (fun u v -> pred u (app f [ v ])); (fun u v -> pred (app f [ u ]) v) ])
          unary
      @ List.concat_map
          (fun (h, _) ->
            [ (fun u v -> pred u (app h [ u; v ])); (fun u v -> pred (app h [ u; v ]) v) ])
          binary_fns)
    preds
  @
  if not equality then []
  else
    List.concat_map
      (fun (f, _) ->
        [ (fun u v -> Wire.Eq (app f [ u ], v)); (fun u v -> Wire.Eq (u, app f [ v ])) ])
      unary
    @ List.map (fun (h, _) u v -> Wire.Eq (app h [ u; v ], v)) binary_fns

let diagonal_relations ?(equality = true) ?(binary = true) signature =
  if Signature.is_unrestricted signature then 0
  else 2 * List.length (base_relations ~equality ~binary signature)

(* Diagonal conditions R(x,x) and ~R(x,x) for relation paths R = R1;...;Rk
   (k <= max_length) over the signed base relations, as a LAZY sequence:
   memory is O(k) whatever the signature, and the consumer caps how many it
   takes. Paths are existential compositions; Free 0 is the principal
   variable. Order: by k, then lexicographic over the signed base list, the
   negated condition before the positive one (the Russell shape first). *)
let diagonals ?(max_length = 4) ?(equality = true) ?(binary = true) signature : Wire.source Seq.t =
  if Signature.is_unrestricted signature then Seq.empty
  else
    let base = base_relations ~equality ~binary signature in
    let signed =
      Array.of_list (List.concat_map (fun r -> [ r; (fun u v -> Wire.Neg (r u v)) ]) base)
    in
    let b = Array.length signed in
    (* Intermediates z1..z_{k-1} sit under (k-1) Ex binders: z_i is B (k-1-i). *)
    let path k idx =
      let node i = if i = 0 || i = k then Wire.F 0 else Wire.B (k - 1 - i) in
      let atoms = List.init k (fun i -> signed.(idx.(i)) (node i) (node (i + 1))) in
      let body = match atoms with [ a ] -> a | xs -> Wire.Conj xs in
      let rec wrap j f = if j = 0 then f else wrap (j - 1) (Wire.Ex f) in
      wrap (k - 1) body
    in
    let successor idx =
      let next = Array.copy idx in
      let rec bump i =
        if i < 0 then None
        else if next.(i) + 1 < b then (
          next.(i) <- next.(i) + 1;
          Some next)
        else (
          next.(i) <- 0;
          bump (i - 1))
      in
      bump (Array.length next - 1)
    in
    let rec level k () = if k > max_length || b = 0 then Seq.Nil else paths k (Array.make k 0) ()
    and paths k idx () =
      let f = path k idx in
      let rest = match successor idx with Some n -> paths k n | None -> level (k + 1) in
      Seq.Cons (Wire.Neg f, fun () -> Seq.Cons (f, rest))
    in
    level 1

(* Total number of diagonals of [diagonals] (for reporting caps). *)
let diagonal_count ?(max_length = 4) ?equality ?binary signature =
  let s = diagonal_relations ?equality ?binary signature in
  let rec sum k acc p = if k > max_length then acc else sum (k + 1) (acc + (p * s)) (p * s) in
  2 * sum 1 0 1

(* The prior as the lane's generic hook: the Lawvere diagonals of the run's
   signature, with these grammar bounds. *)
let prior ?(max_length = 4) ?(equality = true) ?(binary = true) () : Probe_lane.prior =
 fun signature -> diagonals ~max_length ~equality ~binary signature

(* Structural checks of the generator (formerly in the library's lane tests;
   run by [schema_bench prior-check] under dune runtest): the sequence is lazy,
   [diagonal_count] matches it, it reaches the k = 4 cycle and the injection
   shape, its first condition is the Russell shape, and an unrestricted
   signature has none. Raises Failure otherwise. *)
let check () =
  let check b message = if not b then failwith ("lawvere: " ^ message) in
  let sg = Signature.make ~functions:[ ("g", 1); ("a", 0) ] ~predicates:[ ("member", 2) ] in
  let count = diagonal_count ~max_length:4 sg in
  check (Seq.length (diagonals ~max_length:4 sg) = count) "diagonal_count disagrees";
  (* 12 signed relations (member: 4 shapes x 2 signs, plus 2 equalities x 2). *)
  check (diagonal_relations sg = 12) "unexpected base relation count";
  let big =
    Signature.make
      ~functions:[ ("f", 1); ("g", 1); ("h", 2); ("k", 2) ]
      ~predicates:[ ("p", 2); ("q", 2); ("r", 2) ]
  in
  check (diagonal_count ~max_length:6 big > 1_000_000_000) "test signature too small";
  (match diagonals ~max_length:6 big () with
  | Seq.Cons (Wire.Neg (Wire.Pred ("p", [ Wire.F 0; Wire.F 0 ])), _) -> ()
  | _ -> failwith "lawvere: the first diagonal is not the Russell shape");
  let injection =
    Wire.Ex
      (Wire.Conj
         [
           Wire.Eq (Wire.F 0, Wire.App ("g", [ Wire.B 0 ]));
           Wire.Neg (Wire.Pred ("member", [ Wire.F 0; Wire.B 0 ]));
         ])
  in
  check (Seq.exists (( = ) injection) (diagonals ~max_length:2 sg)) "no Cantor-injection shape";
  let cycle4 =
    let m x y = Wire.Pred ("member", [ x; y ]) in
    Wire.Neg
      (Wire.Ex
         (Wire.Ex
            (Wire.Ex
               (Wire.Conj
                  [
                    m (Wire.F 0) (Wire.B 2);
                    m (Wire.B 2) (Wire.B 1);
                    m (Wire.B 1) (Wire.B 0);
                    m (Wire.B 0) (Wire.F 0);
                  ]))))
  in
  check (Seq.exists (( = ) cycle4) (diagonals ~max_length:4 Signature.sets)) "no 4-cycle";
  check (Seq.length (diagonals Signature.unrestricted) = 0) "diagonals over unrestricted";
  Printf.printf "prior-check: %d diagonals (k <= 4) over the g/a/member signature\n%!" count
