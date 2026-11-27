open Axiom_fuzzer
open Test_support
open Wire

(* Ported E heuristics: generators, admissible KBO, selection, evaluation, queue
   mix, and end-to-end kernel-checked refutations. *)

let fn name args = Fn (Original name, args)
let c name = fn name []
let x = V (0, 0)
let y = V (0, 1)
let eq a b = E (a, b)

let installed ?unified table =
  let order = Ordering.create () in
  Ordering.install_table ?unified order table;
  order

let fkey name arity = (Ordering.Function (Original name), arity)
let ranks table key = fst (Hashtbl.find table key)
let weight table key = snd (Hashtbl.find table key)

(* Frequencies: f/1 x4, g/1 x1, h/2 x2, a x3, b x1, p/1 x2. *)
let signature_clauses =
  [
    [ positive (eq (fn "f" [ fn "f" [ c "a" ] ]) (fn "h" [ c "a"; c "b" ])) ];
    [ negative (P ("p", [ fn "f" [ x ] ])); positive (P ("p", [ fn "g" [ x ] ])) ];
    [ positive (eq (fn "f" [ c "a" ]) (fn "h" [ x; x ])) ];
  ]

let random_term rng depth =
  let syms = [| ("f", 1); ("g", 1); ("h", 2); ("k", 3); ("a", 0); ("b", 0) |] in
  let rec go d =
    if d = 0 || Random.State.int rng 4 = 0 then
      if Random.State.bool rng then V (0, Random.State.int rng 3)
      else c (if Random.State.bool rng then "a" else "b")
    else
      let name, arity = syms.(Random.State.int rng (Array.length syms)) in
      fn name (List.init arity (fun _ -> go (d - 1)))
  in
  go depth

let rec subterms t = t :: (match t with V _ -> [] | Fn (_, ts) -> List.concat_map subterms ts)

(* Clauses with at most one variable are variants exactly when their normal forms agree. *)
let same a b = Clause.normalize a = Clause.normalize b

(* Golden values from E 3.5.9 itself: LPO4 orientations of 120 random term pairs (depth 3 over
   f/1, g/1, h/2, k/3, a, b, c and X, Y, Z, non-unifiable sides, Python random seed 20261115). Each
   pair is a negative unit s != t after a header clause in which every symbol occurs. E ran this
   problem, and the same problem with every pair written t != s, with --term-ordering=LPO4
   --print-saturated and each configuration's precedence option (--precedence=<chain> or
   -G<generator>), and printed every processed literal greater side first: ">" s > t (both runs
   print s first), "<" t > s, "?" incomparable (each run keeps its written order), "-" E deleted the
   pair as subsumed by another one. The generators agree with E only with E's own first-occurrence
   ranks (Eorder.e_pos_ranks). *)
let lpo_pairs =
  {|cnf(header, axiom, p(k(a,b,c), h(f(a),g(b)))).
cnf(c0, axiom, k(g(k(c,a,Z)),Y,c) != h(g(h(a,c)),h(h(b,b),h(X,a)))).
cnf(c1, axiom, b != k(f(Y),h(h(a,Y),h(a,c)),Z)).
cnf(c2, axiom, h(f(k(Y,a,c)),f(k(a,Z,b))) != f(f(g(a)))).
cnf(c3, axiom, f(g(g(b))) != b).
cnf(c4, axiom, f(g(Z)) != h(h(a,g(Y)),a)).
cnf(c5, axiom, k(g(g(b)),h(a,h(a,Y)),f(c)) != k(k(f(c),g(b),f(X)),X,h(g(a),k(a,a,Z)))).
cnf(c6, axiom, k(h(h(c,a),Y),g(f(Y)),b) != b).
cnf(c7, axiom, g(b) != f(h(g(Z),g(Z)))).
cnf(c8, axiom, c != h(f(f(a)),f(f(Y)))).
cnf(c9, axiom, b != k(b,X,h(k(c,Z,b),g(c)))).
cnf(c10, axiom, f(k(g(b),g(Y),k(Y,c,a))) != g(Z)).
cnf(c11, axiom, a != f(h(k(b,b,Z),k(X,b,a)))).
cnf(c12, axiom, k(X,g(f(c)),c) != b).
cnf(c13, axiom, h(f(k(a,X,b)),h(k(X,b,b),h(a,X))) != k(h(b,k(c,Y,a)),f(k(b,Z,Y)),g(X))).
cnf(c14, axiom, f(k(Y,b,g(b))) != Y).
cnf(c15, axiom, b != c).
cnf(c16, axiom, f(a) != a).
cnf(c17, axiom, k(b,g(h(Y,b)),f(f(Z))) != g(f(h(c,X)))).
cnf(c18, axiom, k(g(c),Y,g(c)) != f(g(k(Z,Z,Z)))).
cnf(c19, axiom, k(f(a),X,k(c,g(a),g(b))) != f(k(g(Z),a,b))).
cnf(c20, axiom, h(c,h(f(Y),h(Z,X))) != h(k(b,h(b,c),g(b)),k(Z,b,X))).
cnf(c21, axiom, f(f(g(X))) != k(c,X,b)).
cnf(c22, axiom, h(h(b,f(c)),g(c)) != a).
cnf(c23, axiom, b != g(h(Z,g(b)))).
cnf(c24, axiom, h(c,k(c,f(a),h(b,b))) != h(k(g(b),k(Z,X,b),X),X)).
cnf(c25, axiom, k(h(X,g(c)),f(g(Z)),X) != c).
cnf(c26, axiom, g(g(k(X,Y,X))) != g(h(f(b),g(Y)))).
cnf(c27, axiom, g(h(g(c),X)) != g(f(g(b)))).
cnf(c28, axiom, h(g(k(c,c,b)),h(g(X),k(c,a,X))) != a).
cnf(c29, axiom, h(g(g(a)),f(f(a))) != g(g(g(Z)))).
cnf(c30, axiom, f(a) != b).
cnf(c31, axiom, k(b,Z,c) != b).
cnf(c32, axiom, k(a,h(g(X),c),k(Y,b,c)) != k(g(k(Z,c,c)),h(a,g(c)),f(h(Z,Y)))).
cnf(c33, axiom, g(k(h(b,Z),c,b)) != h(g(c),h(g(Y),g(c)))).
cnf(c34, axiom, g(f(g(a))) != k(c,f(g(c)),b)).
cnf(c35, axiom, k(k(k(X,b,Y),h(a,b),g(Y)),f(k(X,X,c)),X) != h(f(h(b,Y)),h(f(Z),k(Y,Y,b)))).
cnf(c36, axiom, h(g(h(a,X)),Y) != f(a)).
cnf(c37, axiom, c != g(k(h(Z,b),g(a),f(X)))).
cnf(c38, axiom, g(Y) != k(h(k(Z,a,b),h(a,a)),X,k(h(c,Y),g(c),f(a)))).
cnf(c39, axiom, h(h(X,g(Z)),h(k(Z,c,b),f(X))) != f(Z)).
cnf(c40, axiom, g(f(g(Y))) != f(f(g(X)))).
cnf(c41, axiom, b != g(f(c))).
cnf(c42, axiom, c != g(g(f(X)))).
cnf(c43, axiom, c != h(k(k(b,b,c),g(c),g(b)),h(h(b,a),a))).
cnf(c44, axiom, k(c,k(f(Z),g(b),X),f(h(a,c))) != c).
cnf(c45, axiom, g(c) != a).
cnf(c46, axiom, k(a,k(a,Z,b),f(Z)) != h(h(Z,f(Y)),k(g(a),g(Z),g(Z)))).
cnf(c47, axiom, f(Y) != g(g(b))).
cnf(c48, axiom, k(h(g(c),f(Y)),a,g(k(b,b,c))) != k(f(h(a,Y)),h(f(a),g(Y)),b)).
cnf(c49, axiom, h(f(g(Y)),k(h(Y,c),h(Y,a),k(c,X,X))) != f(c)).
cnf(c50, axiom, k(h(g(c),f(Y)),g(g(Y)),g(f(b))) != g(g(f(Z)))).
cnf(c51, axiom, k(k(k(Y,X,a),Y,g(c)),k(a,k(X,Z,Y),f(X)),h(g(Z),f(X))) != k(f(f(Z)),g(b),f(f(a)))).
cnf(c52, axiom, h(f(h(Z,b)),g(c)) != f(h(Z,h(c,a)))).
cnf(c53, axiom, Y != k(f(X),k(k(X,X,Y),h(c,a),h(a,c)),k(Z,g(a),h(Y,b)))).
cnf(c54, axiom, k(k(X,k(a,a,a),k(X,c,c)),k(g(c),k(Y,c,Z),f(c)),k(a,Y,b)) != f(k(h(b,a),k(b,b,Y),g(Z)))).
cnf(c55, axiom, h(a,f(h(X,a))) != k(h(g(a),h(Y,a)),f(h(b,c)),f(f(a)))).
cnf(c56, axiom, f(g(h(X,b))) != g(h(f(b),g(c)))).
cnf(c57, axiom, g(c) != k(g(k(X,X,c)),b,c)).
cnf(c58, axiom, h(g(g(b)),f(f(c))) != b).
cnf(c59, axiom, g(g(f(a))) != h(f(f(Z)),k(a,X,h(X,c)))).
cnf(c60, axiom, a != k(Z,k(k(Y,c,X),f(Y),b),f(f(b)))).
cnf(c61, axiom, f(k(h(c,Z),c,h(Y,a))) != h(b,a)).
cnf(c62, axiom, f(g(f(a))) != f(g(g(X)))).
cnf(c63, axiom, k(c,Z,g(f(Y))) != h(k(k(b,b,a),k(b,a,X),f(b)),k(g(c),Z,g(b)))).
cnf(c64, axiom, g(h(X,k(c,Z,c))) != k(h(f(Y),g(c)),b,f(c))).
cnf(c65, axiom, k(f(f(b)),g(k(a,a,b)),g(h(Y,c))) != a).
cnf(c66, axiom, k(k(k(b,b,X),Y,h(Z,X)),h(g(c),c),b) != f(f(c))).
cnf(c67, axiom, f(k(f(c),h(Z,Z),h(c,c))) != g(a)).
cnf(c68, axiom, b != h(X,a)).
cnf(c69, axiom, g(h(g(b),k(a,a,a))) != a).
cnf(c70, axiom, g(Z) != k(f(k(c,b,Y)),X,b)).
cnf(c71, axiom, f(g(h(a,b))) != g(X)).
cnf(c72, axiom, g(a) != f(c)).
cnf(c73, axiom, g(X) != k(Y,h(a,h(b,Y)),b)).
cnf(c74, axiom, h(g(h(a,Y)),g(h(Y,X))) != a).
cnf(c75, axiom, g(a) != k(g(k(Y,b,Z)),g(h(c,a)),a)).
cnf(c76, axiom, f(h(c,k(c,a,a))) != g(b)).
cnf(c77, axiom, k(f(h(b,Z)),f(h(c,c)),Y) != a).
cnf(c78, axiom, f(c) != f(g(k(Y,c,b)))).
cnf(c79, axiom, f(f(k(c,b,b))) != k(h(h(b,Z),h(a,Z)),g(h(b,Y)),Y)).
cnf(c80, axiom, g(k(a,f(X),b)) != k(h(h(X,X),h(Y,Z)),k(a,h(c,Z),g(b)),c)).
cnf(c81, axiom, g(c) != h(a,X)).
cnf(c82, axiom, k(Z,b,k(b,h(c,Y),k(Y,c,X))) != f(k(c,X,Z))).
cnf(c83, axiom, b != k(g(b),a,g(X))).
cnf(c84, axiom, X != f(k(g(X),b,k(c,b,c)))).
cnf(c85, axiom, k(h(X,h(a,Y)),k(g(c),Z,f(Z)),f(a)) != k(h(g(c),a),h(k(c,c,b),k(b,Z,Y)),X)).
cnf(c86, axiom, g(g(k(b,a,b))) != g(a)).
cnf(c87, axiom, f(h(f(X),f(a))) != a).
cnf(c88, axiom, f(f(f(X))) != g(h(a,h(b,c)))).
cnf(c89, axiom, k(f(Z),h(g(a),f(X)),c) != k(h(g(a),k(a,a,a)),g(g(X)),g(g(b)))).
cnf(c90, axiom, g(f(f(b))) != a).
cnf(c91, axiom, g(k(k(X,b,b),f(c),X)) != f(a)).
cnf(c92, axiom, g(h(k(Y,c,c),h(Y,Z))) != k(f(g(b)),c,h(h(b,b),b))).
cnf(c93, axiom, h(k(h(c,Z),b,k(X,b,a)),g(k(a,Y,c))) != h(X,k(k(c,b,b),g(c),g(X)))).
cnf(c94, axiom, k(b,g(Y),c) != f(b)).
cnf(c95, axiom, f(f(Y)) != h(k(h(Z,a),f(c),Z),k(c,g(c),f(a)))).
cnf(c96, axiom, f(h(f(c),k(c,b,X))) != X).
cnf(c97, axiom, f(Z) != g(f(f(b)))).
cnf(c98, axiom, g(g(h(Y,a))) != g(h(g(X),h(c,a)))).
cnf(c99, axiom, k(c,h(k(a,c,a),h(b,a)),f(h(X,a))) != c).
cnf(c100, axiom, f(f(c)) != h(h(f(Z),k(b,a,c)),h(k(c,X,a),f(b)))).
cnf(c101, axiom, f(c) != h(c,f(b))).
cnf(c102, axiom, a != c).
cnf(c103, axiom, h(h(k(Z,a,Z),k(a,Y,c)),f(f(b))) != g(f(b))).
cnf(c104, axiom, f(k(g(b),Y,f(a))) != f(f(a))).
cnf(c105, axiom, k(h(g(Z),Z),h(c,X),X) != g(f(b))).
cnf(c106, axiom, h(h(h(X,X),k(c,Y,Z)),Z) != k(f(f(a)),k(h(c,X),k(Y,b,a),h(b,Z)),b)).
cnf(c107, axiom, c != h(f(g(c)),k(f(Y),h(a,X),g(b)))).
cnf(c108, axiom, f(g(g(X))) != g(h(h(c,c),g(Y)))).
cnf(c109, axiom, f(Z) != g(X)).
cnf(c110, axiom, f(h(f(Y),Y)) != g(h(Y,h(X,a)))).
cnf(c111, axiom, k(k(g(b),g(b),g(Z)),k(k(b,b,c),k(Y,Z,b),b),k(g(b),X,k(c,Z,a))) != a).
cnf(c112, axiom, k(f(h(c,c)),k(c,h(b,Z),X),g(f(b))) != f(g(b))).
cnf(c113, axiom, X != f(f(f(X)))).
cnf(c114, axiom, k(g(h(X,Z)),h(g(c),g(b)),g(h(Y,X))) != f(g(h(b,b)))).
cnf(c115, axiom, c != h(k(h(a,Y),f(b),g(X)),k(h(X,X),g(c),h(c,c)))).
cnf(c116, axiom, h(g(h(b,c)),c) != k(a,f(f(a)),k(a,h(b,a),b))).
cnf(c117, axiom, h(g(k(Z,c,a)),k(k(a,X,X),c,k(Z,Z,a))) != k(g(k(Z,Y,a)),Z,g(f(Z)))).
cnf(c118, axiom, k(g(X),h(k(b,b,Z),h(c,a)),f(X)) != h(X,g(k(c,a,b)))).
cnf(c119, axiom, k(k(f(Z),X,f(Y)),f(c),h(k(Y,b,c),k(Y,Y,Y))) != f(f(h(a,b)))).|}

let e_lpo4_orientations =
  [
    ( "explicit k>h>g>f>c>b>a",
      "?<>>??>-<<-<>?><>????<><<>>>>?>>??<?><<>-<<<>><->>??><>?-<><<><??>>-<>?--?><-><<<<?<<?>>-?>-??>?>-?><<<>>><<-<->><><<?>>"
    );
    ( "explicit a>f>k>b>h>c>g",
      "?<?>??>-<<-<>?>>>????><<?>??>?>>??>??<<?-<<<><?-<>??<<??-<>??>???>?-<>?--?><-?<<?<?<<>>>-?<-????>-?><<>>>?<<-<->?<?<<???"
    );
    ( "invarity",
      "?<?>??>-<<-<>?><>?????<<?>?>>?>>??>?><?>-<?<><<-<>??<<??-<>??>???>>-<>?--?><-?<<?<?<<?>>-?<->?>?>-?><>>>>>?<-<->><><<???"
    );
    ( "invfreqconstmin",
      "?<?>??>-<<-<>?>>>???>>><?>??>?>>??<??<<?-<<<>>?-<>??<<??-<><<>???>?-<>?--?><-><??<?<<?>>->>-?>??>-?>?<<>>??<-<->><?<<?>?"
    );
    ( "arity",
      "?<>>??>-<<-<>?><>????<><<>>>>?>>??<?><<>-<<<>><->>??><>?-<><<><??>>-<>?--?><-><<<<?<<?>>-?>-??>?>-?><<>>>><<-<->><><<?>>"
    );
    ( "invfreq",
      "?<?>??>-<<-<>?><>?????<<?>?>>?>>??>??<<?-<?<><?-<>??<<??-<>??>???>?-<>?--?><-?<<?<?<<?>>-?<->>>?>-?><>>>>>?<-<->><><<???"
    );
  ]

(* A TPTP term without spaces: upper-case names are the variables X, Y, Z. *)
let parse_term text =
  let pos = ref 0 in
  let rec term () =
    let start = !pos in
    while
      !pos < String.length text
      && match text.[!pos] with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false
    do
      incr pos
    done;
    let name = String.sub text start (!pos - start) in
    if Char.uppercase_ascii name.[0] = name.[0] then
      V (0, match name with "X" -> 0 | "Y" -> 1 | "Z" -> 2 | _ -> failwith name)
    else if !pos < String.length text && text.[!pos] = '(' then (
      let args = ref [] in
      let continue = ref true in
      while !continue do
        incr pos;
        args := term () :: !args;
        continue := text.[!pos] = ','
      done;
      incr pos;
      fn name (List.rev !args))
    else c name
  in
  term ()

(* A group whose elements are their own inverses is commutative: every complete strategy refutes
   the negated conjecture quickly. The scheduling costs run on a stopped clock, so that each search
   is the same on a loaded machine; the wall limit only bounds a broken run. *)
let group_problem =
  "cnf(c1,axiom,(f(X,e) = X)). cnf(c2,axiom,(f(e,X) = X)). cnf(c3,axiom,(f(X,X) = e)).\n\
   cnf(c4,axiom,(f(f(X,Y),Z) = f(X,f(Y,Z)))).\n\
   cnf(c5,negated_conjecture,(f(a,b) != f(b,a)))."

let group_runner () =
  let t = Tptp.parse group_problem in
  let run strategies workers =
    let config =
      {
        Scheduler.default_config with
        reference = false;
        portfolio = Strategy.Workers (List.map Strategy.of_name strategies);
        engine =
          {
            Engine.default_config with
            goal_names = [ "c5" ];
            limits = { Engine.default_limits with seconds = 300. };
          };
      }
    in
    let saved = !Engine.cost_clock in
    (Engine.cost_clock := fun () -> 0.);
    let r =
      Fun.protect
        ~finally:(fun () -> Engine.cost_clock := saved)
        (fun () -> Scheduler.portfolio ~workers config (fun () -> Theory.copy t))
    in
    match r.certificate with
    | None -> failwith (String.concat "," strategies ^ ": no refutation: " ^ r.reason)
    | Some cert ->
        check
          (Result.is_ok (Kernel.check t cert))
          (String.concat "," strategies ^ ": kernel rejected")
  in
  (t, run)

(* The strategies the default search can reach: production and the diversified members. *)
let default_strategies =
  "production" :: List.map (fun (s : Strategy.t) -> s.name) Strategy.diversified

(* The evaluation tier (heuristic_tests.exe --eval, the runtest-eval alias): every other complete
   member. A SInE-filtered member is incomplete by design: here SInE keeps only associativity (the
   identity and inverse axioms are triggered by e, which no reached axiom contains). A Vampire
   slice with a set of support never lets two axioms meet (incomplete). *)
let eval_tests =
  [
    ( "every complete evaluation member finds a kernel-checked refutation",
      fun () ->
        let _, run = group_runner () in
        List.iter
          (fun (h : Heuristic.t) ->
            match h.vampire with
            | Some v when not (Vampire.complete v) -> ()
            | _ ->
                if h.sine_filter = None && not (List.mem h.name default_strategies) then
                  run [ h.name ] 1)
          Heuristic.named );
  ]

let tests =
  [
    ( "LPO4 orients 106 random term pairs as E 3.5.9 does under six precedences",
      fun () ->
        let lines = List.tl (String.split_on_char '\n' lpo_pairs) in
        let pairs =
          List.map
            (fun line ->
              let body = String.sub line 0 (String.length line - 2) in
              let body =
                let i = String.index body ',' in
                let j = String.index_from body (i + 1) ',' in
                String.trim (String.sub body (j + 1) (String.length body - j - 1))
              in
              let i = String.index body '!' in
              ( parse_term (String.trim (String.sub body 0 i)),
                parse_term (String.trim (String.sub body (i + 2) (String.length body - i - 2))) ))
            lines
        in
        equal (List.length pairs) 120 "pairs";
        let clauses =
          List.concat_map (Clausify.run ~mode:Hybrid) (Theory.fixed (Tptp.parse lpo_pairs))
        in
        (* An explicit precedence chain, greatest symbol first (E's --precedence). *)
        let explicit chain =
          let names = List.rev (String.split_on_char '>' chain) in
          let tbl = Hashtbl.create 8 in
          List.iteri
            (fun i name ->
              let arity =
                Option.value ~default:0
                  (List.assoc_opt name [ ("f", 1); ("g", 1); ("h", 2); ("k", 3) ])
              in
              Hashtbl.replace tbl (fkey name arity) (i + 1, 1))
            names;
          let order = Ordering.create () in
          Ordering.install_table ~unified:true ~kind:Lpo order tbl;
          order
        in
        let generated precedence =
          let order = Ordering.create () in
          ignore (Eorder.install (Heuristic.lpo4 precedence) order clauses);
          order
        in
        let compared = ref 0 and ambiguous = ref [] in
        List.iter
          (fun (config, codes) ->
            let order =
              match config with
              | "invarity" -> generated Invarity
              | "invfreqconstmin" -> generated Invfreq_constmin
              | "arity" -> generated Arity
              | "invfreq" -> generated Invfreq
              | _ -> explicit (List.nth (String.split_on_char ' ' config) 1)
            in
            List.iteri
              (fun i (s, t) ->
                let e = codes.[i] in
                if e <> '-' then (
                  incr compared;
                  let ours =
                    if Ordering.greater ~order s t then '>'
                    else if Ordering.greater ~order t s then '<'
                    else '?'
                  in
                  (* E prints an incomparable pair in its own order when both runs keep one
                     side first, so "?" against ">" or "<" is not a disagreement. *)
                  if ours = '?' && e <> '?' then ambiguous := i :: !ambiguous
                  else equal ours e (Printf.sprintf "%s: pair c%d" config i)))
              pairs)
          e_lpo4_orientations;
        equal !compared 636 "compared pairs";
        (* Only c109, f(Z) != g(X), which no LPO orients: E printed g(X) first in both runs. *)
        equal (List.sort_uniq compare !ambiguous) [ 109 ] "ambiguous pairs" );
    ( "E invfreqhack puts the most frequent unary symbol on top and constants at the bottom",
      fun () ->
        let table, violations =
          Eorder.table
            {
              ordering = Kbo;
              precedence = Invfreq_hack;
              weights = Unit_weights;
              const_weight = 0;
              e_signature = false;
              e_ranks = false;
            }
            signature_clauses
        in
        equal violations [] "unit weights are admissible";
        let r = ranks table in
        check (r (fkey "f" 1) > r (fkey "g" 1)) "max-frequency unary f must top g";
        check (r (fkey "f" 1) > r (fkey "h" 2)) "max-frequency unary f must top h";
        check (r (fkey "g" 1) > r (fkey "h" 2)) "rarer g must be above more frequent h";
        check
          (r (fkey "a" 0) < r (fkey "h" 2) && r (fkey "b" 0) < r (fkey "g" 1))
          "constants must be minimal";
        (* Constants: key2 = -freq, so the frequent a is below b. *)
        check (r (fkey "a" 0) < r (fkey "b" 0)) "invfreqhack orders constants by frequency" );
    ( "E invfreq precedence and invfreqrank weights follow symbol frequencies",
      fun () ->
        let table, violations =
          Eorder.table
            {
              ordering = Kbo;
              precedence = Invfreq;
              weights = Invfreq_rank;
              const_weight = 1;
              e_signature = false;
              e_ranks = false;
            }
            signature_clauses
        in
        equal violations [] "invfreqrank is admissible";
        let r = ranks table and w = weight table in
        check (r (fkey "f" 1) < r (fkey "h" 2)) "frequent f must be below h";
        check (r (fkey "h" 2) < r (fkey "g" 1)) "h must be below the rare g";
        equal (w (fkey "f" 1)) 1 "the most frequent symbol weighs 1";
        check (w (fkey "g" 1) > w (fkey "h" 2)) "rarer symbols weigh more";
        equal (w (fkey "a" 0)) 1 "constants weigh to_const_weight" );
    ( "aritymax0 gives the top unary symbol weight 0 and the KBO orients f(x) > x",
      fun () ->
        let table, violations =
          Eorder.table
            {
              ordering = Kbo;
              precedence = Invfreq_hack;
              weights = Arity_max0;
              const_weight = 0;
              e_signature = false;
              e_ranks = false;
            }
            signature_clauses
        in
        equal violations [] "the top unary symbol may weigh 0";
        equal (weight table (fkey "f" 1)) 0 "f must weigh 0";
        equal (weight table (fkey "h" 2)) 3 "arity weights are arity + 1";
        let order = installed table in
        check (Ordering.greater ~order (fn "f" [ x ]) x) "f(x) > x";
        check (Ordering.greater ~order (fn "f" [ fn "f" [ x ] ]) (fn "f" [ x ])) "f(f(x)) > f(x)";
        check
          (Ordering.greater ~order (fn "f" [ fn "g" [ x ] ]) (fn "g" [ fn "f" [ x ] ]))
          "the weight-0 symbol is greatest";
        check (not (Ordering.greater ~order x (fn "f" [ x ]))) "x is not above f(x)";
        (* A symbol first seen after installation stays below the weight-0 top. *)
        check
          (Ordering.greater ~order (fn "f" [ fn "new" [ x ] ]) (fn "new" [ fn "f" [ x ] ]))
          "unknown symbols must rank below the weight-0 symbol";
        check
          (not (Ordering.greater (fn "f" [ x ]) (fn "f" [ fn "f" [ x ] ])))
          "the standard order is untouched" );
    ( "inadmissible weight-0 unary symbols are repaired",
      fun () ->
        let w = Hashtbl.create 4 in
        Hashtbl.replace w (fkey "f" 1) 0;
        Hashtbl.replace w (fkey "g" 1) 1;
        Hashtbl.replace w (fkey "a" 0) 0;
        let rank = function k when k = fkey "g" 1 -> 3 | k when k = fkey "f" 1 -> 2 | _ -> 1 in
        let violations = Eorder.admissible ~rank w in
        equal (List.length violations) 2 "a non-maximal weight-0 unary and a 0 constant";
        equal (Hashtbl.find w (fkey "f" 1)) 1 "f repaired";
        equal (Hashtbl.find w (fkey "a" 0)) 1 "a repaired" );
    ( "randomized: generated KBO instances are admissible strict orders with the subterm property",
      fun () ->
        let rng = Random.State.make [| 20261114 |] in
        let configs =
          List.concat_map
            (fun precedence ->
              List.map
                (fun weights ->
                  {
                    Eorder.ordering = Kbo;
                    precedence;
                    weights;
                    const_weight = 0;
                    e_signature = false;
                    e_ranks = false;
                  })
                [ Eorder.Unit_weights; Precedence_weights; Invfreq_rank; Arity_weights; Arity_max0 ])
            [ Eorder.Invfreq; Invfreq_hack; Arity; Invfreq_constmin ]
          |> List.concat_map (fun config ->
              [ config; { config with Eorder.e_signature = not config.Eorder.e_signature } ])
        in
        List.iter
          (fun config ->
            for _ = 1 to 6 do
              let clauses =
                List.init 4 (fun _ -> [ positive (eq (random_term rng 3) (random_term rng 3)) ])
              in
              let table, _ = Eorder.table config clauses in
              (* Re-checking a repaired table finds nothing left to repair. *)
              let w = Hashtbl.create 16 in
              Hashtbl.iter (fun k (_, wt) -> Hashtbl.replace w k wt) table;
              let rank k = Option.fold ~none:0 ~some:fst (Hashtbl.find_opt table k) in
              equal (Eorder.admissible ~rank w) [] "a generated table needed repair";
              let order = installed ~unified:config.e_signature table in
              let greater = Ordering.greater ~order in
              for _ = 1 to 60 do
                let s = random_term rng 4 and t = random_term rng 4 and u = random_term rng 3 in
                check (not (greater s s)) "irreflexive";
                check (not (greater s t && greater t s)) "asymmetric";
                if greater s t && greater t u then check (greater s u) "transitive";
                List.iter
                  (fun sub -> if sub <> s then check (greater s sub) "subterm property")
                  (subterms s)
              done
            done)
          configs );
    ( "E selection functions choose E's literals",
      fun () ->
        (* SelectMaxLComplexAvoidPosPred: a unique maximal literal means no selection. *)
        equal
          (Eselection.max_l_complex_avoid_pos_pred
             (Clause.normalize
                [
                  negative (P ("p", [ c "a" ])); positive (P ("q", [ fn "f" [ fn "f" [ c "a" ] ] ]));
                ]))
          None "unique maximal literal";
        (* PSelectComplexExceptUniqMaxHorn on a non-Horn clause: a negative pure-variable
           literal wins. *)
        let clause =
          Clause.normalize
            [
              negative (eq x y);
              negative (P ("p", [ fn "f" [ x ] ]));
              positive (P ("q", [ x; y ]));
              positive (P ("r", [ y; x ]));
            ]
        in
        let pure =
          Option.get
            (List.find_index
               (fun l -> (not l.positive) && match l.atom with E (V _, V _) -> true | _ -> false)
               clause)
        in
        equal
          (Eselection.p_complex_except_uniq_max_horn clause)
          (Some [ pure ]) "pure variable literal";
        (* Without pure or ground negatives, the most unbalanced negative and every positive. *)
        let clause =
          Clause.normalize
            [
              negative (eq (fn "f" [ fn "f" [ x ] ]) y);
              negative (eq (fn "g" [ x ]) (fn "g" [ y ]));
              positive (P ("q", [ x; y ]));
              positive (P ("r", [ x ]));
            ]
        in
        let unbalanced =
          Option.get (List.find_index (fun l -> l.atom = eq (fn "f" [ fn "f" [ x ] ]) y) clause)
        in
        let positives =
          List.filter_map
            (fun (i, l) -> if l.positive then Some i else None)
            (List.mapi (fun i l -> (i, l)) clause)
        in
        equal
          (Eselection.p_complex_except_uniq_max_horn clause)
          (Some (List.sort compare (unbalanced :: positives)))
          "PSelectDiffNegativeLiteral";
        (* SelectNewComplexAHP never selects a type literal P(X). *)
        equal
          (Eselection.new_complex_ahp
             (Clause.normalize [ negative (P ("t", [ x ])); positive (P ("q", [ x ])) ]))
          None "type literals are forbidden";
        let clause =
          Clause.normalize
            [
              negative (P ("t", [ fn "f" [ x ] ]));
              negative (P ("u", [ c "a" ]));
              positive (P ("q", [ x ]));
            ]
        in
        let ground = Option.get (List.find_index (fun l -> l.atom = P ("u", [ c "a" ])) clause) in
        equal (Eselection.new_complex_ahp clause) (Some [ ground ]) "ground literals first" );
    ( "Refinedweight and ConjectureRelativeSymbolWeight reproduce E's arithmetic",
      fun () ->
        (* Golden values derived by hand from E's definitions, not from the port's flags.
           Refinedweight(3,2,2,1.5,2) weighs a literal TermWeight(lterm, vweight 2, fweight 3)
           * max_term 2 (a predicate literal has no rterm term), * 1.5 when maximal, * 2 when
           positive. In ~p(f(f(f(X)))) | q(h(X)) | r(X) the negative literal (lterm 4*3+2 = 14,
           28) exceeds both positive literals (q(h(X)): 2*3+2 = 8, 16; r(X): 3+2 = 5, 10) in the
           standard KBO, and q(h(X)) > r(X). *)
        let clause =
          Clause.normalize
            [
              negative (P ("p", [ fn "f" [ fn "f" [ fn "f" [ x ] ] ] ]));
              positive (P ("q", [ fn "h" [ x ] ]));
              positive (P ("r", [ x ]));
            ]
        in
        let facts =
          {
            Evaluation.initial = true;
            sos = false;
            processed = false;
            conjecture = None;
            age = 7;
            level = 0;
            relevance = None;
          }
        in
        let refined =
          Evaluation.Refined
            { fweight = 3; vweight = 2; max_term = 2.; max_literal = 1.5; positive = 2. }
        in
        let queues =
          [
            { Evaluation.count = 1; priority = Simulate_sos; weight = refined };
            { count = 1; priority = Const_prio; weight = Fifo };
            { count = 1; priority = Prefer_non_goals; weight = Fifo };
          ]
        in
        let evaluate ?selection facts = Evaluation.evaluate ?selection queues facts clause in
        (* An initial clause is evaluated before any selection (ProofStateInit): only the
           negative literal is maximal. 28 * 1.5 + 16 * 2 + 10 * 2 = 94. *)
        let evals = evaluate ~selection:Eselection.P_complex_except_uniq_max_horn facts in
        equal evals.(0) (Evaluation.prio_normal, 94.) "initial Refinedweight(SimulateSOS)";
        equal evals.(1) (Evaluation.prio_normal, 7.) "FIFOWeight";
        equal (fst evals.(2)) Evaluation.prio_prefer "a clause with a positive literal is no goal";
        (* A derived clause is evaluated after its selection. PSelectComplexExceptUniqMaxHorn
           selects the negative literal and both positive ones; E's LiteralCompare makes the
           selected literals of opposite sign incomparable, so ~p(..) and q(h(X)) are maximal
           and r(X) is not: 28 * 1.5 + 16 * 1.5 * 2 + 10 * 2 = 110. *)
        equal
          (Eselection.p_complex_except_uniq_max_horn clause)
          (Some [ 0; 1; 2 ])
          "P selection of every positive literal";
        let derived = { facts with initial = false } in
        let evals = evaluate ~selection:Eselection.P_complex_except_uniq_max_horn derived in
        equal evals.(0) (Evaluation.prio_defer, 110.) "derived Refinedweight after P selection";
        (* Without a selection function, every clause keeps its KBO-maximal literals. *)
        equal (snd (evaluate derived).(0)) 94. "no selection: KBO maximality";
        (* SimulateSOS gives PrioNormal to set-of-support clauses as well as initial ones. *)
        equal
          (fst (evaluate ~selection:P_complex_except_uniq_max_horn { derived with sos = true }).(0))
          Evaluation.prio_normal "set-of-support clauses are not deferred";
        (* SelectMaxLComplexAvoidPosPred selects nothing when one literal is maximal. *)
        equal
          (snd (evaluate ~selection:Max_l_complex_avoid_pos_pred derived).(0))
          94. "no selection keeps KBO maximality";
        (* CRSW(0.5, 100 ...): conjecture symbols weigh 50. ~q(a) alone, a conjecture symbol. *)
        let unit = [ negative (P ("q", [ c "a" ])) ] in
        let crsw conjecture =
          snd
            (Evaluation.evaluate
               [ { count = 1; priority = Const_prio; weight = Heuristic.crsw 0.5 1. } ]
               { facts with conjecture } unit).(0)
        in
        (* lterm q(a): 100 + 100 = 200 * 1.5; rterm $true 100; maximal * 1.5. *)
        equal (crsw None) ((100. +. (200. *. 1.5)) *. 1.5) "no conjecture symbols";
        let only_a key = key = (Ordering.Function (Original "a"), 0) in
        equal (crsw (Some only_a)) ((100. +. (150. *. 1.5)) *. 1.5) "conjecture constant weighs 50"
    );
    ( "the E queue mix serves its queues with their counts in order",
      fun () ->
        let q = Passive.create ~mix:[ 1; 4; 1; 1; 4 ] ~ratio:10 () in
        for id = 0 to 99 do
          Passive.add
            ~evals:(Array.init 5 (fun i -> (40, float_of_int (id * (i + 3) mod 17))))
            q id 1
        done;
        let served = ref [] in
        for _ = 1 to 22 do
          let before = Passive.mix_selections q in
          ignore (Passive.take q);
          let after = Passive.mix_selections q in
          Array.iteri (fun i n -> if n <> before.(i) then served := i :: !served) after
        done;
        equal (List.rev !served)
          [ 0; 1; 1; 1; 1; 2; 3; 4; 4; 4; 4; 0; 1; 1; 1; 1; 2; 3; 4; 4; 4; 4 ]
          "HCBStandardClauseSelect order";
        equal (Passive.length q) 78 "each selection removes one live clause";
        check
          (q.weight = Passive.Empty && q.age = Passive.Empty && q.unit_weight = Passive.Empty)
          "a queue mix filled the production heaps";
        (* Collection keeps the stale entries of a mix until they dominate; the order of
           selection is the same either way. *)
        let heaps (q : Passive.t) = (Option.get q.mix).heaps in
        let before = Array.copy (heaps q) in
        Passive.compact q;
        check (heaps q = before) "compaction rebuilt a mix without dominant stale entries";
        let next q = List.init 10 (fun _ -> Passive.take q) in
        let r = Passive.create ~mix:[ 1; 4; 1; 1; 4 ] ~ratio:10 () in
        for id = 0 to 99 do
          Passive.add
            ~evals:(Array.init 5 (fun i -> (40, float_of_int (id * (i + 3) mod 17))))
            r id 1
        done;
        for _ = 1 to 22 do
          ignore (Passive.take r)
        done;
        Passive.rebuild r;
        equal (next q) (next r) "a rebuild changed the selection order" );
    ( "a clause that re-enters a queue mix is ordered by its new evaluation after a rebuild",
      fun () ->
        (* Presaturation returns active clauses to Passive under their own ids with new
           evaluations ([Engine.end_presat]); the entries of their first evaluations stay in the
           heaps that never popped them (lazy deletion) and select by the old keys until the mix is
           rebuilt. Two queues, each weighing a clause by its evaluation order. *)
        let evals order = [| (40, float_of_int order); (40, float_of_int order) |] in
        let run rebuild =
          let q = Passive.create ~mix:[ 1; 1 ] ~ratio:10 () in
          Passive.add ~evals:(evals 1) ~order:1 q 10 1;
          Passive.add ~evals:(evals 2) ~order:2 q 20 1;
          (* Queue 0 pops 10; queue 1 skips 10's dead entry and pops 20: queue 0 keeps 20's first
             entry. *)
          let a = Passive.take q in
          let b = Passive.take q in
          let first = [ a; b ] in
          Passive.add ~evals:(evals 3) ~order:3 q 10 1;
          Passive.add ~evals:(evals 4) ~order:4 q 20 1;
          if rebuild then Passive.rebuild q;
          (first, Passive.take q)
        in
        equal (run true) ([ Some 10; Some 20 ], Some 10) "the new evaluations after a rebuild";
        equal (snd (run false)) (Some 20) "the fixture keeps a stale first entry without one" );
    ( "an E queue mix starts at its queue phase, and phases repeat with the mix period",
      fun () ->
        let served ~phase counts n =
          let q = Passive.create ~phase ~mix:counts ~ratio:10 () in
          let queues = List.length counts in
          for id = 0 to 99 do
            Passive.add
              ~evals:(Array.init queues (fun i -> (40, float_of_int (id * (i + 3) mod 17))))
              q id 1
          done;
          List.init n (fun _ ->
              let before = Passive.mix_selections q in
              let id = Passive.take q in
              let after = Passive.mix_selections q in
              let queue = ref (-1) in
              Array.iteri (fun i k -> if k <> before.(i) then queue := i) after;
              (!queue, id))
        in
        let mix = [ 1; 4; 1; 1; 4 ] in
        let cycle = [ 0; 1; 1; 1; 1; 2; 3; 4; 4; 4; 4 ] in
        for phase = 0 to 24 do
          let queues = List.map fst (served ~phase mix 22) in
          equal queues
            (List.init 22 (fun s -> List.nth cycle ((phase + s) mod 11)))
            (Printf.sprintf "phase %d does not start at its position" phase)
        done;
        (* Phase 0 is E's own start; congruent phases select the same clauses. *)
        equal (List.map fst (served ~phase:0 mix 11)) cycle "phase 0 left E's order";
        equal (served ~phase:3 mix 40) (served ~phase:14 mix 40) "phases 3 and 14 differ";
        check (served ~phase:0 mix 40 <> served ~phase:1 mix 40) "phases 0 and 1 select alike";
        equal (Passive.mix_period mix) 11 "208 mix period";
        equal (Passive.mix_period [ 20; 5; 1 ]) 26 "Y1346 mix period";
        equal (Passive.mix_period [ 3 ]) 1 "a single queue has no phase";
        check
          (rejects (fun () -> ignore (Passive.mix_period [ 1; 0 ])))
          "an empty count was accepted";
        (* The production turns: 22 for the default ratio 10, with or without the unit queue. *)
        equal (Passive.turn_period ~policy:Passive.Mixed ~ratio:10 ()) 22 "production period";
        equal (Passive.turn_period ~policy:Passive.Size ~ratio:10 ()) 22 "size-only period";
        equal (Passive.turn_period ~plain:true ~ratio:10 ()) 11 "plain queues period";
        equal (Passive.turn_period ~ratio:0 ()) 1 "age only" );
    ( "destructive equality resolution replaces a clause with a kernel-checked instance",
      fun () ->
        let t =
          Tptp.parse "cnf(a,axiom,(X != f(b) | p(X))). cnf(n,negated_conjecture,(~p(f(b))))."
        in
        List.iter
          (fun strategy ->
            let events = ref [] in
            let e =
              Engine.create
                ~on_clause:(fun stage _ (s : step) -> events := (stage, s) :: !events)
                { Engine.default_config with strategy = Strategy.of_name strategy }
            in
            Engine.prepare_ordering e (Theory.fixed t);
            List.iter (Engine.add_axiom e) (Theory.fixed t);
            Engine.finish e;
            let events = List.rev !events in
            let input =
              List.find_map
                (fun (stage, (s : step)) ->
                  match (stage, s.rule) with
                  | "derived", Input _ when List.length s.clause = 2 -> Some s
                  | _ -> None)
                events
              |> Option.get
            in
            (* The input clause is replaced at once: retired by forward simplification and
               never a given clause. *)
            check
              (List.exists (fun (stage, (s : step)) -> stage = "reduced" && s.id = input.id) events)
              (strategy ^ ": the input clause was not retired");
            check
              (not
                 (List.exists
                    (fun (stage, (s : step)) ->
                      (stage = "selected" || stage = "active" || stage = "retained")
                      && s.id = input.id)
                    events))
              (strategy ^ ": the replaced clause was kept");
            (* Its replacement p(f(b)) is the equality-resolution step binding X to f(b). *)
            let replacement =
              List.find_map
                (fun (stage, (s : step)) ->
                  match (stage, s.rule) with
                  | "derived", Equality_resolve (parent, _, sigma) when parent = input.id ->
                      Some (s, sigma)
                  | _ -> None)
                events
            in
            (match replacement with
            | Some (s, [ (_, Fn (Original "f", [ Fn (Original "b", []) ])) ]) ->
                equal s.clause
                  [ positive (P ("p", [ fn "f" [ c "b" ] ])) ]
                  (strategy ^ ": wrong replacement")
            | _ -> failwith (strategy ^ ": no binding equality-resolution replacement"));
            match Engine.certificate e ~theory:(Theory.name t) with
            | None -> failwith (strategy ^ ": " ^ Engine.reason e)
            | Some cert ->
                check (Result.is_ok (Kernel.check t cert)) (strategy ^ ": kernel rejected"))
          [ "e208"; "sat001" ] );
    ( "P-selected positive literals are paramodulation targets only, as in E",
      fun () ->
        let step id clause = { id; clause = Clause.normalize clause; rule = Input (id, 0) } in
        let collect run =
          let found = ref [] in
          run (fun clause _ -> found := Clause.normalize clause :: !found);
          !found
        in
        let e208 =
          Calculus.create ~ordered:true ~strategy:(Strategy.of_name "e208") (Term.create ())
        in
        let h t = fn "h" [ t ] in
        (* ~p(X) | q(h(X)) | r(X): q(h(X)) is the strictly maximal literal, selected with r(X)
           and ~p(X) by PSelectDiffNegativeLiteral. *)
        let c2 =
          step 0
            [ negative (P ("p", [ x ])); positive (P ("q", [ h x ])); positive (P ("r", [ x ])) ]
        in
        equal (Calculus.selected e208 c2) (Some [ 0; 1; 2 ]) "P selection";
        let unit = step 1 [ negative (P ("q", [ h (c "a") ])) ] in
        equal
          (collect (Calculus.resolve e208 c2 unit) @ collect (Calculus.resolve e208 unit c2))
          [] "a P-selected positive literal resolved";
        (* ~p(X) | h(h(X)) = X | q(X): no superposition from the selected equation. *)
        let c3 =
          step 2 [ negative (P ("p", [ x ])); positive (eq (h (h x)) x); positive (P ("q", [ x ])) ]
        in
        check (Calculus.selected e208 c3 <> None) "c3 selects";
        let target = step 3 [ negative (P ("r", [ h (h (c "a")) ])) ] in
        equal (collect (Calculus.paramodulate e208 c3 target)) [] "superposition from a P literal";
        (* Superposition into q(h(X)) under a larger selected negative literal: only the other
           selected positive literal r(X) is compared, as in E's LiteralCompare. *)
        let c4 =
          step 4
            [
              negative (P ("p", [ fn "f" [ fn "f" [ fn "f" [ x ] ] ] ]));
              positive (P ("q", [ h x ]));
              positive (P ("r", [ x ]));
            ]
        in
        let rule = step 5 [ positive (eq (h y) y) ] in
        let expected =
          Clause.normalize
            [
              negative (P ("p", [ fn "f" [ fn "f" [ fn "f" [ x ] ] ] ]));
              positive (P ("q", [ x ]));
              positive (P ("r", [ x ]));
            ]
        in
        check
          (List.exists (fun k -> same k expected) (collect (Calculus.paramodulate e208 rule c4)))
          "no superposition into a maximal P-selected literal";
        (* Factoring stays available, as E's equality factoring of maximal literals. *)
        let c5 =
          step 6
            [ negative (P ("p", [ x ])); positive (P ("q", [ x ])); positive (P ("q", [ c "a" ])) ]
        in
        let factors = collect (Calculus.unary e208 c5) in
        check
          (List.exists
             (fun k -> same k [ negative (P ("p", [ c "a" ])); positive (P ("q", [ c "a" ])) ])
             factors)
          "factoring of P-selected literals was lost";
        (* Production keeps resolving from a selected positive literal (its lookahead may
           select one): the restriction belongs to the ported heuristics. *)
        let production = Calculus.create ~ordered:true (Term.create ()) in
        Tbl.Int.replace production.selected c2.id (Some [ 0; 1 ]);
        check
          (collect (Calculus.resolve production c2 unit) <> [])
          "production lost a selected positive literal" );
    ( "E's set of support: goal clauses and every descendant, through inferences and simplification",
      fun () ->
        let t =
          Tptp.parse
            "cnf(a1,axiom,(p(X) | q(X))). cnf(a2,axiom,(~q(X) | r(X))). cnf(a3,axiom,(~r(X) | \
             s(X))). cnf(a4,axiom,(f(f(X)) = f(X))). cnf(g1,negated_conjecture,(~p(f(f(a))))). \
             cnf(g2,negated_conjecture,(~s(f(a))))."
        in
        let e =
          Engine.create
            { Engine.default_config with strategy = Strategy.of_name "e208"; collect_every = 0 }
        in
        Engine.prepare_ordering e (Theory.fixed t);
        List.iter (Engine.add_axiom e) (Theory.fixed t);
        Engine.finish e;
        check (e.root <> None) "no refutation";
        let expected = Hashtbl.create 64 in
        let rec sos id =
          match Hashtbl.find_opt expected id with
          | Some b -> b
          | None ->
              let s = Proof.get e.proof id in
              let b =
                match s.rule with
                | Input _ -> not (List.exists (fun l -> l.positive) s.clause)
                | rule -> List.exists sos (Wire.parents rule)
              in
              Hashtbl.replace expected id b;
              b
        in
        let marked = ref 0 and unmarked = ref 0 in
        for id = 0 to Proof.length e.proof - 1 do
          match Proof.get e.proof id with
          | exception Not_found -> ()
          | _ ->
              let b = sos id in
              if b then incr marked else incr unmarked;
              equal (Hashtbl.mem e.sos_ids id) b (Printf.sprintf "set of support of step %d" id)
        done;
        check (!marked > 2 && !unmarked > 2) "the fixture does not exercise both cases";
        (* The rewritten goal ~p(f(a)) inherits the flag from its goal parent. *)
        check
          (List.exists
             (fun id ->
               let s = Proof.get e.proof id in
               s.clause = [ negative (P ("p", [ fn "f" [ c "a" ] ])) ])
             (List.of_seq (Hashtbl.to_seq_keys e.sos_ids)))
          "the rewritten goal left the set of support" );
    ( "ported strategies finish each given clause before the next (BOO002-1 within 150 given)",
      fun () ->
        (* Ternary Boolean algebra: TPTP BOO002-1, read from its verbatim TPTP v10.0.0 file
           (attribution and terms: THIRD-PARTY.md). E 3.5.9 needs 81-128 processed clauses with
           these heuristics; interleaving suspended inferences with new given clauses needed
           more than 270. *)
        let t = Tptp.parse (tptp_problem "Problems/BOO/BOO002-1.p") in
        List.iter
          (fun (h : Heuristic.t) ->
            let config =
              {
                Scheduler.default_config with
                reference = false;
                engine =
                  {
                    Engine.default_config with
                    strategy = Strategy.of_name h.name;
                    goal_names = [ "prove_equation" ];
                    limits =
                      {
                        Engine.seconds = 30.;
                        max_given = 150;
                        max_generated = 1_000_000;
                        max_retained = 1_000_000;
                      };
                  };
              }
            in
            let r = Scheduler.run config t in
            match r.certificate with
            | None -> failwith (h.name ^ ": " ^ r.reason)
            | Some cert -> check (Result.is_ok (Kernel.check t cert)) (h.name ^ ": kernel rejected"))
          Heuristic.named );
    ( "a lean worker's normal form is iterated rewrite_once, one checked Paramodulate per step",
      fun () ->
        (* f(a) -> b, g(b,X) -> h(X), h(h(X)) -> X: p(g(f(a),h(g(f(a),c)))) reaches p(h(c)) in five
           leftmost-outermost steps, two of them at the root after the clause changed below it. *)
        let e = Engine.create { Engine.default_config with strategy = Strategy.of_name "e208" } in
        let axiom i clause = Engine.record e clause (Input (i, 0)) in
        let rules =
          [
            [ positive (eq (fn "f" [ c "a" ]) (c "b")) ];
            [ positive (eq (fn "g" [ c "b"; x ]) (fn "h" [ x ])) ];
            [ positive (eq (fn "h" [ fn "h" [ x ] ]) x) ];
          ]
        in
        let demodulators = List.mapi axiom rules in
        List.iter (Demodulation.add e.demodulator) demodulators;
        let target =
          axiom 3
            [
              positive
                (P
                   ( "p",
                     [ fn "g" [ fn "f" [ c "a" ]; fn "h" [ fn "g" [ fn "f" [ c "a" ]; c "c" ] ] ] ]
                   ));
            ]
        in
        let rec iterate (s : step) n =
          match Demodulation.rewrite_once e.demodulator s with
          | None -> (s.clause, n)
          | Some (clause, rule) ->
              iterate { id = 1000 + n; clause = Clause.normalize clause; rule } (n + 1)
        in
        let expected, steps = iterate target 0 in
        equal steps 5 "the fixture needs five rewrite steps";
        equal expected [ positive (P ("p", [ fn "h" [ c "c" ] ])) ] "iterated normal form";
        let stored = Proof.stored e.proof in
        match Engine.normal_form e target with
        | None -> failwith "no rewrite"
        | Some { clause; rule; using } ->
            equal (Clause.normalize clause) expected
              "the normal form differs from iterated rewriting";
            equal e.metrics.normal_form_steps 5 "rewrite steps";
            equal e.metrics.normal_form_chains 1 "chains";
            equal (Proof.stored e.proof - stored) 4 "four proof-only intermediates";
            equal using
              (List.sort compare (List.map (fun (s : step) -> s.id) demodulators))
              "every demodulator of the chain retires the target";
            (* Every intermediate and the result are kernel derivations of their parents. *)
            let inputs = List.mapi (fun i r -> (i, [ r ])) (rules @ [ target.clause ]) in
            let nodes = List.init (Proof.stored e.proof) (Proof.get e.proof) in
            let derive rule = Kernel.derive ~inputs ~steps:nodes rule in
            List.iter
              (fun (s : step) ->
                match s.rule with
                | Paramodulate _ ->
                    equal (derive s.rule) (Ok s.clause)
                      "an intermediate is not its rule's conclusion";
                    check
                      ((Tbl.Int.find e.avatar.entries s.id).role = Avatar.Retired)
                      "an intermediate is a search candidate"
                | _ -> ())
              nodes;
            equal (derive rule) (Ok expected) "the result is not its rule's conclusion" );
    ( "lean normal forms: no rewrite intermediate is admitted and no simplified given is queued",
      fun () ->
        let problem =
          "cnf(left_identity,axiom,mult(e,X)=X). cnf(left_inverse,axiom,mult(inv(X),X)=e). \
           cnf(associativity,axiom,mult(mult(X,Y),Z)=mult(X,mult(Y,Z))). \
           cnf(cube,axiom,mult(X,mult(X,X))=e). \
           cnf(goal,negated_conjecture,mult(a,mult(b,mult(a,mult(b,mult(a,b)))))!=e)."
        in
        let t = Tptp.parse problem in
        check
          (Engine.default_config.normal_form && not Engine.default_config.given_at_once)
          "a lean worker's default is normal-form rewriting with queued replacements";
        let run name normal_form given_at_once =
          let config =
            {
              Scheduler.default_config with
              reference = false;
              (* The switches of the ported lean loop (the members' E loop processes a simplified
                 given at once whatever [given_at_once] says). *)
              loop = Some Heuristic.loop_ported;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name name;
                  goal_names = [ "goal" ];
                  normal_form;
                  given_at_once;
                  limits = { Engine.default_limits with seconds = 30.; max_given = 2000 };
                };
            }
          in
          let r = Scheduler.run config t in
          (match r.certificate with
          | None -> failwith (name ^ ": " ^ r.reason)
          | Some cert -> check (Result.is_ok (Kernel.check t cert)) (name ^ ": kernel rejected"));
          r.engine.metrics
        in
        List.iter
          (fun (h : Heuristic.t) ->
            let on = run h.name true true and off = run h.name false false in
            equal on.rewrite_reentries 0 (h.name ^ ": a rewrite intermediate ran the admission");
            equal on.given_requeued 0 (h.name ^ ": a simplified given clause was queued");
            check (off.rewrite_reentries > 0) (h.name ^ ": the fixture has no rewrite chain");
            equal off.normal_form_chains 0 (h.name ^ ": one-step admission rewrote a chain");
            equal off.given_at_once 0 (h.name ^ ": one-step admission processed a replacement");
            check
              (on.normal_form_steps > on.normal_form_chains)
              (h.name ^ ": no chain of two or more steps");
            (* Production keeps the one-step admission whatever the switches say. *)
            let production = run "production" true true in
            equal production.normal_form_chains 0 "production rewrote to normal form";
            equal production.given_at_once 0 "production processed a replacement at once")
          [ Heuristic.e208; Heuristic.y1346; Heuristic.sat001 ] );
    ( "the selection trace lists every lean selection and changes nothing",
      fun () ->
        let problem =
          "cnf(c1,axiom,(f(X,e) = X)). cnf(c2,axiom,(f(e,X) = X)). cnf(c3,axiom,(f(X,X) = e)).\n\
           cnf(c4,axiom,(f(f(X,Y),Z) = f(X,f(Y,Z)))).\n\
           cnf(c5,negated_conjecture,(f(a,b) != f(b,a)))."
        in
        let t = Tptp.parse problem in
        let run () =
          let config =
            {
              Scheduler.default_config with
              reference = false;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name "sat001";
                  goal_names = [ "c5" ];
                  limits = { Engine.default_limits with seconds = 30. };
                };
            }
          in
          let r = Scheduler.run config t in
          check (r.certificate <> None) "no refutation";
          (r.engine.metrics.given, r.engine.metrics.generated, r.engine.metrics.processed)
        in
        let lines = ref [] in
        let plain = run () in
        Engine.given_trace := Some (fun line -> lines := line :: !lines);
        let traced = Fun.protect ~finally:(fun () -> Engine.given_trace := None) run in
        equal traced plain "the trace changed the search";
        let given, _, processed = traced in
        let fields = List.rev_map (String.split_on_char '\t') !lines in
        equal
          (List.length
             (List.filter (fun f -> String.starts_with ~prefix:"processed" (List.nth f 3)) fields))
          processed "processed lines";
        equal
          (List.sort_uniq compare (List.map (fun f -> int_of_string (List.nth f 1)) fields))
          (List.init given (fun i -> i + 1))
          "one selection number per given clause";
        check
          (List.for_all (fun f -> List.length f = 8 && List.hd f = "sat001") fields)
          "line format" );
    ( "PreferGoals, PNRefinedweight and prefer_initial_clauses evaluate as in E",
      fun () ->
        (* ~p(f(X)) | q(a). PNRefinedweight(PreferGoals,1,1,3,5,2,1,0.5): the negative literal weighs
           (3 + 3 + 5) * 2 = 22 with the negative weights, the positive one (1 + 1) * 2 * 0.5 = 2.
           Refinedweight with the positive weights: (1 + 1 + 1) * 2 + 2 = 8. A max_literal factor
           of 1 keeps maximality out of the numbers. *)
        let clause =
          Clause.normalize [ negative (P ("p", [ fn "f" [ x ] ])); positive (P ("q", [ c "a" ])) ]
        in
        let pn =
          Evaluation.Pn_refined
            {
              fweight = 1;
              vweight = 1;
              nfweight = 3;
              nvweight = 5;
              max_term = 2.;
              max_literal = 1.;
              positive = 0.5;
            }
        and refined =
          Evaluation.Refined
            { fweight = 1; vweight = 1; max_term = 2.; max_literal = 1.; positive = 0.5 }
        in
        let queues =
          [
            { Evaluation.count = 1; priority = Prefer_goals; weight = pn };
            { count = 1; priority = Prefer_goals; weight = refined };
          ]
        in
        let facts =
          {
            Evaluation.initial = false;
            sos = false;
            processed = false;
            conjecture = None;
            age = 3;
            level = 0;
            relevance = None;
          }
        in
        let evals = Evaluation.evaluate queues facts clause in
        equal evals.(0) (Evaluation.prio_normal, 24.) "PNRefinedweight of a non-goal";
        equal evals.(1) (Evaluation.prio_normal, 8.) "Refinedweight of a non-goal";
        let goal = [ negative (P ("p", [ fn "f" [ x ] ])) ] in
        equal
          (Evaluation.evaluate queues facts goal).(0)
          (Evaluation.prio_prefer, 22.) "a clause without positive literals is a goal";
        (* prefer_initial_clauses lowers every priority of an initial clause only. *)
        let initial = { facts with initial = true } in
        let boosted = Evaluation.evaluate ~prefer_initial:true queues initial clause in
        equal
          (fst boosted.(0))
          (Evaluation.prio_normal - Evaluation.prio_largest_reasonable)
          "initial clauses come first";
        equal
          (fst boosted.(1))
          (Evaluation.prio_normal - Evaluation.prio_largest_reasonable)
          "in every queue";
        equal
          (fst (Evaluation.evaluate ~prefer_initial:true queues facts clause).(0))
          Evaluation.prio_normal "derived clauses keep their priority";
        equal
          (fst (Evaluation.evaluate queues initial clause).(0))
          Evaluation.prio_normal "only with prefer_initial_clauses";
        (* The LPO members: E's LPO4 instances, kernel-checked refutations of a rewrite system
           whose duplicating rule KBO orients the other way. *)
        List.iter
          (fun name ->
            let order =
              match (Strategy.of_name name).precedence with
              | E_instance e -> e
              | _ -> (Heuristic.find name).order
            in
            check (order.ordering = Lpo && order.e_ranks) (name ^ ": not E's LPO4 instance"))
          [ "h042"; "h047b31"; "calc:lpo" ];
        let problem =
          "cnf(r1,axiom,(double(X) = plus(X,X))). cnf(r2,axiom,(plus(zero,X) = X)).\n\
           cnf(goal,negated_conjecture,(double(zero) != zero))."
        in
        let t = Tptp.parse problem in
        let clauses = List.concat_map (Clausify.run ~mode:Hybrid) (Theory.fixed t) in
        let lpo = Ordering.create () in
        ignore (Eorder.install (Heuristic.find "h042").order lpo clauses);
        let dx = fn "double" [ x ] and pxx = fn "plus" [ x; x ] in
        check (Ordering.greater ~order:lpo dx pxx) "LPO: double(X) > plus(X,X)";
        check (Ordering.greater pxx dx) "KBO: plus(X,X) > double(X)";
        List.iter
          (fun name ->
            let config =
              {
                Scheduler.default_config with
                reference = false;
                engine =
                  {
                    Engine.default_config with
                    strategy = Strategy.of_name name;
                    goal_names = [ "goal" ];
                    limits = { Engine.default_limits with seconds = 20.; max_given = 200 };
                  };
              }
            in
            let r = Scheduler.run config t in
            match r.certificate with
            | None -> failwith (name ^ ": " ^ r.reason)
            | Some cert -> check (Result.is_ok (Kernel.check t cert)) (name ^ ": kernel rejected"))
          [ "h042"; "h047b31"; "calc:lpo" ] );
    ( "the default strategies and portfolios find kernel-checked refutations",
      fun () ->
        let _, run = group_runner () in
        let roles = snd (Tptp.parse_annotated group_problem) in
        equal (List.assoc "c5" roles) "negated_conjecture" "roles are threaded";
        List.iter (fun name -> run [ name ] 1) default_strategies;
        run [ "production"; "e208"; "y1346"; "sat001" ] 4;
        run [ "production"; "e208k"; "y1346k"; "sat001k" ] 4;
        run [ "production"; "e208"; "y1346"; "production" ] 4;
        (* The recommended composition: production on queue phases 1 and 3. *)
        run [ "e208"; "production"; "y1346"; "production" ] 4;
        check (rejects (fun () -> ignore (Strategy.of_name "nonsense"))) "unknown strategy";
        (* A deterministic ported strategy is never replicated across workers at one queue
           phase: copies run at phases 0, 1, ... (their copy index), at most its period (11 for
           e208) of them. *)
        let e208 = Strategy.of_name "e208" in
        run [ "e208"; "production"; "e208"; "production" ] 4;
        check
          (rejects (fun () -> ignore (Strategy.assign Strategy.Uniform ~base:e208 ~workers:12 0)))
          "replicated e208 workers at one phase";
        check
          (Strategy.assign Strategy.Uniform ~base:e208 ~workers:2 1 == e208)
          "two e208 workers at distinct phases were refused";
        check
          (Strategy.assign Strategy.Uniform ~base:e208 ~workers:1 0 == e208)
          "one e208 worker was refused";
        check
          (rejects (fun () ->
               ignore
                 (Strategy.assign
                    (Strategy.Workers (Strategy.production :: List.init 12 (fun _ -> e208)))
                    ~base:Strategy.production ~workers:13 0)))
          "e208 repeated at one phase in a worker list" );
    ( "member candidates: E's non-P SelectComplexExceptUniqMaxHorn and SelectCQArNT",
      fun () ->
        let order = Ordering.create () in
        (* Non-Horn, two negative literals, no pure-variable or ground negative literal: the
           most unbalanced negative literal; the P variant adds every positive literal. *)
        let clause =
          [
            negative (P ("p", [ fn "f" [ fn "f" [ x ] ] ]));
            negative (eq (fn "f" [ x ]) y);
            positive (P ("q", [ x ]));
            positive (P ("r", [ y ]));
          ]
        in
        let p = Eselection.select ~order Eselection.P_complex_except_uniq_max_horn clause in
        let n = Eselection.select ~order Eselection.Complex_except_uniq_max_horn clause in
        check (Option.map List.length p = Some 3) "the P variant selects the positive literals";
        check
          (match (n, p) with
          | Some [ i ], Some js -> List.mem i js && not (List.nth clause i).positive
          | _ -> false)
          "the non-P variant selects the same single negative literal";
        (* SelectCQArNT: the negative literal with the highest-arity head (an equation counts as
           arity 2), then the alphabetically first head. *)
        let clause =
          [
            negative (P ("b", [ x ]));
            negative (P ("z", [ x; y; x ]));
            negative (P ("a", [ x; y; y ]));
            negative (eq x (c "k"));
            positive (P ("q", [ x ]));
          ]
        in
        check (Eselection.select ~order Eselection.Cq_ar_nt clause = Some [ 2 ]) "CQArNT: a/3";
        check
          (Eselection.select ~order Eselection.Cq_ar_nt
             [ negative (P ("b", [ x ])); negative (eq x (c "k")) ]
          = Some [ 1 ])
          "CQArNT: an equation (arity 2) before a unary predicate" );
    ( "Vampire's selection 10: a negative equation first, then the heaviest negative literal",
      fun () ->
        let clause =
          [
            positive (P ("q", [ fn "f" [ fn "f" [ fn "f" [ x ] ] ] ]));
            negative (P ("p", [ fn "f" [ fn "f" [ x ] ] ]));
            negative (P ("r", [ x ]));
          ]
        in
        check (Ordering.vampire_best_10 clause = Some 1) "the heaviest negative literal";
        check
          (Ordering.vampire_best_10 (clause @ [ negative (eq x (c "a")) ]) = Some 3)
          "a negative equation before heavier predicate literals";
        check (Ordering.vampire_best_10 [ positive (P ("q", [ x ])) ] = None) "no negative literal";
        check
          ((Strategy.of_name "calc:v10").selection = Strategy.Vampire_best_10
          && not (List.memq (Strategy.of_name "calc:v10") Strategy.diversified))
          "calc:v10 is an evaluation member" );
    ( "invfreqconjmax puts the conjecture symbols on top and invprecedence weighs by rank",
      fun () ->
        let kbo precedence weights =
          {
            Eorder.ordering = Kbo;
            precedence;
            weights;
            const_weight = 1;
            e_signature = false;
            e_ranks = false;
          }
        in
        (* g/1 occurs once, in the conjecture; f/1 four times. *)
        let conjecture (key : Ordering.head * int) = key = fkey "g" 1 in
        let plain, _ = Eorder.table (kbo Invfreq Inv_precedence) signature_clauses in
        let conj, _ =
          Eorder.table ~conjecture (kbo Invfreq_conjmax Inv_precedence) signature_clauses
        in
        let without, _ = Eorder.table (kbo Invfreq_conjmax Inv_precedence) signature_clauses in
        let top table =
          Hashtbl.fold
            (fun k (r, _) (bk, br) -> if r > br then (k, r) else (bk, br))
            table
            (fkey "a" 0, -1)
          |> fst
        in
        check (top conj = fkey "g" 1) "the conjecture symbol is the greatest";
        check
          (Hashtbl.fold (fun k v ok -> ok && Hashtbl.find_opt without k = Some v) plain true)
          "without roles invfreqconjmax is invfreq";
        (* invprecedence: the greatest symbol weighs 1, every other one more. *)
        check (weight conj (fkey "g" 1) = 1) "the top symbol weighs 1";
        check (weight conj (fkey "f" 1) > 1) "a smaller symbol weighs more" );
    ( "SInE levels: goal 0, triggered axioms by distance, unreachable axioms marked, no filtering",
      fun () ->
        let ax id clauses goal = (id, clauses, goal) in
        let levels =
          Sine_levels.compute
            [
              ax 0 [ [ negative (P ("p", [ c "a" ])) ] ] true;
              ax 1 [ [ positive (P ("p", [ x ])); negative (P ("q", [ x ])) ] ] false;
              ax 2 [ [ positive (P ("q", [ c "b" ])) ] ] false;
              ax 3 [ [ positive (P ("r", [ c "d" ])) ] ] false;
            ]
        in
        match levels with
        | None -> failwith "levels expected"
        | Some l ->
            check (Sine_levels.level l 0 = 0) "goal level 0";
            check (Sine_levels.level l 1 = 1) "p triggers axiom 1";
            check (Sine_levels.level l 2 = 2) "q (level 1) triggers axiom 2";
            check (Sine_levels.level l 3 = Sine_levels.unreached) "axiom 3 is unreachable";
            check (Sine_levels.level l 99 = Sine_levels.unreached) "a later axiom is unreached";
            check
              (Sine_levels.compute [ ax 0 [ [ positive (P ("p", [ c "a" ])) ] ] false ] = None)
              "no negated conjecture, no levels" );
    ( "the SInE layer queue prefers reachable clauses and keeps the base order inside the layer",
      fun () ->
        let facts level =
          {
            Evaluation.initial = false;
            sos = false;
            processed = false;
            conjecture = None;
            age = 1;
            level;
            relevance = None;
          }
        in
        let q = { Evaluation.count = 1; priority = Const_prio; weight = Fifo } in
        let mix = Evaluation.layered ~cutoff:Sine_levels.reachable ~ratio:2 [ q ] in
        check (List.length mix = 2 && (List.nth mix 1).count = 2) "a plain copy and a 2x layer copy";
        check (Evaluation.uses_levels mix && not (Evaluation.uses_levels [ q ])) "uses_levels";
        let clause = [ positive (P ("p", [ c "a" ])) ] in
        let eval level = Evaluation.evaluate mix (facts level) clause in
        check
          (fst (eval 3).(0) = fst (eval Sine_levels.unreached).(0))
          "the plain queue ignores levels";
        check
          (fst (eval 3).(1) < fst (eval Sine_levels.unreached).(1))
          "the layer queue defers unreached";
        check (fst (eval 0).(1) = fst (eval 3).(1)) "inside the layer the base priority decides";
        let h = Heuristic.find "e208sl" in
        check (Evaluation.uses_levels h.queues) "e208sl reads levels";
        check
          (List.length h.queues = 2 * List.length Heuristic.e208.queues)
          "e208sl doubles the e208 queues" );
    ( "E's loop removes a resolved literal t != t when a clause is admitted",
      fun () ->
        let t = Tptp.parse "cnf(c, axiom, (p(X) | f(a) != f(a)))." in
        let retained name =
          let e = Engine.create { Engine.default_config with strategy = Strategy.of_name name } in
          Engine.prepare_ordering e (Theory.fixed t);
          List.iter (Engine.add_axiom e) (Theory.fixed t);
          List.map (fun (s : step) -> Clause.normalize s.clause) (Index.all e.retained_index)
        in
        let px = Clause.normalize [ positive (P ("p", [ x ])) ] in
        check (List.mem px (retained "sat001")) "the member kept the resolved literal";
        check
          (not (List.mem px (retained "c18")))
          "the ported loop removed the literal at admission" );
    ( "E's initial evaluation order (UniqWeight, then the canonical clause order)",
      fun () ->
        (* Golden order from E 3.5.9 (G-E--_208 with -H '(1.FIFOWeight(ConstPrio))',
           --presat-simplify=false, -l1) on the definition-free clauses of RNG019-7: E evaluates
           (and so FIFO selects) them in this order; equal UniqWeights break ties by E's canonical
           clause order, in which a variable precedes a function symbol. *)
        let problem =
          (* 8 of the 15 clauses of Axioms/RNG003-0.ax, the include of TPTP RNG019-7, in their
             order, selected from the verbatim TPTP v10.0.0 files (attribution and terms:
             THIRD-PARTY.md). *)
          tptp_problem
            ~only:
              [
                "left_additive_identity";
                "right_additive_identity";
                "left_multiplicative_zero";
                "right_multiplicative_zero";
                "left_additive_inverse";
                "right_additive_inverse";
                "additive_inverse_additive_inverse";
                "commutativity_for_addition";
              ]
            "Problems/RNG/RNG019-7.p"
        in
        let clauses =
          List.concat_map (Clausify.run ~mode:Hybrid) (Theory.fixed (Tptp.parse problem))
        in
        equal (E_initial.order clauses) [ 6; 3; 2; 1; 0; 5; 4; 7 ] "E's initial evaluation order" );
    ( "E's initial order from the problem text: parse-order symbol codes, written variable order",
      fun () ->
        (* Golden order from E 3.5.9 (-H '(1.FIFOWeight(ConstPrio))' --presat-simplify=false
           --ac-handling=None -l1): E evaluates, and FIFO selects, c3 c4 c5 c6 goal c1 c2 c7 c8.
           Its symbol codes follow its parser (arguments before their head symbol), so b precedes
           a and c1's p(Y,X) precedes c2's p(X,Y) by E's variable numbering as written; the
           clausified clauses alone (literals sorted, variables renamed) order them otherwise. *)
        let problem =
          "cnf(c1,axiom,( ~ r(X,Y) | p(Y,X) )).\n\
           cnf(c2,axiom,( ~ r(X,Y) | p(X,Y) )).\n\
           cnf(c3,axiom,q(f(b))).\n\
           cnf(c4,axiom,q(f(a))).\n\
           cnf(c5,axiom,( s(X) | ~ t(X) )).\n\
           cnf(c6,axiom,( t(Y) | ~ s(Y) )).\n\
           cnf(c7,axiom,( g(X,h(Y)) = g(h(Y),X) )).\n\
           cnf(c8,axiom,( g(h(X),Y) = g(Y,h(X)) )).\n\
           cnf(goal,negated_conjecture, ~ q(f(c)))."
        in
        let text = Option.get (E_initial.of_text problem) in
        equal
          (List.map (fun n -> Hashtbl.find text.symbols n) [ "r"; "p"; "b"; "f"; "q"; "a" ])
          [ 23; 24; 25; 26; 27; 28 ] "symbol codes in E's parse order";
        let axioms = Theory.fixed (Tptp.parse problem) in
        let named =
          List.concat_map
            (fun (a : axiom) -> List.map (fun c -> (c, a.name)) (Clausify.run ~mode:Hybrid a))
            axioms
        in
        let names = List.map (fun (_, n) -> Some n) named in
        let order = E_initial.order ~text ~names (List.map fst named) in
        let by_name = List.map (fun i -> snd (List.nth named i)) order in
        equal by_name
          [ "c3"; "c4"; "c5"; "c6"; "goal"; "c1"; "c2"; "c7"; "c8" ]
          "E's initial evaluation order from the text";
        check (E_initial.order (List.map fst named) <> order) "the clauses alone order otherwise" );
    ( "E loop details: names, presaturation and the HEN012-1 refutation without binary rewriting \
       and on the ported loop",
      fun () ->
        check (Heuristic.loop_of_string "ported" = Heuristic.loop_ported) "ported";
        check (Heuristic.loop_of_string "e" = Heuristic.loop_e) "e";
        check (Heuristic.loop_of_string "presat" = Heuristic.loop_presat) "presat";
        let some = Heuristic.loop_of_string "e_calculus,presat" in
        check (some.e_calculus && some.presat && not some.discount) "a list sets its fields";
        check
          (match Heuristic.loop_of_string "nonsense" with
          | _ -> false
          | exception Invalid_argument _ -> true)
          "an unknown detail is refused";
        (* HEN012-1: Contraction's binary rewriting replaced the needed unit quotient(zero,X,zero)
           by its less_equal form (the axioms quotient_less_equal and less_equal_quotient make the
           two literals equivalent), so y1346 on the ported loop saturated without a refutation;
           E (and the DISCOUNT loop) has no binary literal rewriting. The problem is TPTP
           HEN012-1 with its include Axioms/HEN001-0.ax, from the verbatim TPTP v10.0.0 files
           (attribution and terms: THIRD-PARTY.md); the test names its negated conjecture goal. *)
        let t =
          Tptp.parse
            (tptp_problem
               ~rename:[ ("prove_X_less_than_or_equal_to_X", "goal") ]
               "Problems/HEN/HEN012-1.p")
        in
        let run name loop =
          let config =
            {
              Scheduler.default_config with
              reference = false;
              loop = Some loop;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name name;
                  goal_names = [ "goal" ];
                  limits = { Engine.default_limits with seconds = 30.; max_given = 20000 };
                };
            }
          in
          let r = Scheduler.run config t in
          match r.certificate with
          | None -> failwith (name ^ ": " ^ r.reason)
          | Some cert ->
              check (Result.is_ok (Kernel.check t cert)) (name ^ ": kernel rejected");
              r.engine
        in
        ignore (run "y1346" { Heuristic.loop_ported with discount = true });
        (* y1346 alone on the ported loop (loop_ported), with binary rewriting: the default
           equivalence rule keeps quotient(zero,X,zero), since it rewrites only when the retirement
           is a redundancy deletion (Contraction.Redundant), which a unit never is; the legacy rule
           (AXIOM_EQUIVALENCE=legacy) retires it and Passive empties after 81 given. *)
        let alone equivalence =
          Scheduler.run
            {
              Scheduler.default_config with
              reference = false;
              loop = Some Heuristic.loop_ported;
              portfolio = Strategy.Workers [ Strategy.of_name "y1346" ];
              engine =
                {
                  Engine.default_config with
                  goal_names = [ "goal" ];
                  equivalence;
                  limits = { Engine.default_limits with seconds = 30.; max_given = 20000 };
                };
            }
            t
        in
        let r = alone Contraction.Redundant in
        (match r.certificate with
        | None -> failwith ("y1346 on the ported loop: " ^ r.reason)
        | Some cert -> check (Result.is_ok (Kernel.check t cert)) "y1346: kernel rejected");
        equal r.engine.contraction.literal_justified r.engine.contraction.literal_rewritten
          "y1346 retired a clause the equivalence does not make redundant";
        let r = alone Contraction.Legacy in
        check
          (r.certificate = None && r.engine.contraction.literal_units > 0)
          "the legacy rule no longer loses HEN012-1 on the ported loop";
        List.iter
          (fun name ->
            let e = run name Heuristic.loop_presat in
            check (not e.presat_running) (name ^ ": presaturation did not end");
            check (e.evaluations > 0) (name ^ ": no evaluation was counted"))
          [ "e208"; "y1346"; "sat001" ] );
    ( "E's creation order of a given's conclusions: the into-positions in reverse",
      fun () ->
        (* REL029-1 (h047): E superposes converse_idempotence_8 (converse is an involution) into the
           given converse_additivity_9 (converse distributes over join) at the second argument of
           its right side before the first: ComputeFromParamodulants pops the given's
           into-positions from the stack they were collected on (preorder of the lterm), so the
           later position comes first. Both are clauses of Axioms/REL001-0.ax, the include of TPTP
           REL029-1, read from the verbatim TPTP v10.0.0 files (attribution and terms:
           THIRD-PARTY.md). *)
        let input name =
          match
            Theory.fixed (Tptp.parse (tptp_problem ~only:[ name ] "Problems/REL/REL029-1.p"))
          with
          | [ a ] -> List.hd (Clausify.run ~mode:Hybrid a)
          | _ -> failwith name
        in
        let given = { id = 2; clause = input "converse_additivity_9"; rule = Input (0, 0) } in
        let partner = { id = 1; clause = input "converse_idempotence_8"; rule = Input (1, 0) } in
        let get id = if id = 1 then partner else given in
        let code (_, a) = 30 + a in
        let key path =
          E_genorder.key ~order:Ordering.standard ~code ~get given
            (Paramodulate (1, 0, false, 2, 0, path, []))
        in
        check (key [ 1; 1 ] < key [ 1; 0 ]) "the second argument before the first";
        check (key [ 1; 0 ] < key [ 1 ]) "the subterms before the whole side";
        let from_key =
          E_genorder.key ~order:Ordering.standard ~code ~get given
            (Paramodulate (2, 0, false, 1, 0, [ 0 ], []))
        in
        check (from_key < key [ 1; 1 ]) "the given as the from clause comes first";
        check
          (E_genorder.key ~order:Ordering.standard ~code ~get given (Equality_resolve (2, 0, []))
          < from_key)
          "equality resolution before paramodulation" );
    ( "E's literal order of a processed clause decides selection ties",
      fun () ->
        (* ClauseSubsumeOrderSortLits: positive literals first, equations first, predicate
           literals by descending symbol code, heavier first, then the previous order. *)
        let a = Fn (Original "a", []) and x = V (0, 0) and y = V (0, 1) in
        let clause =
          [
            negative (P ("p", [ x; y ]));
            negative (P ("r", [ x; y ]));
            positive (P ("q", [ x ]));
            positive (E (x, a));
          ]
        in
        let code = function
          | Ordering.Predicate "p", _ -> 40
          | Ordering.Predicate "r", _ -> 41
          | _ -> 30
        in
        equal (Array.to_list (Eselection.e_rank ~code clause)) [ 3; 2; 1; 0 ] "E's literal order";
        (* SelectNewComplexAHP finds ~p(X,Y) and ~r(X,Y) equally good: E takes ~r, first in its
           order; the sorted clause alone takes ~p. *)
        equal (Eselection.select Eselection.New_complex_ahp clause) (Some [ 0 ]) "own order";
        equal
          (Eselection.select ~rank:(Eselection.e_rank ~code clause) Eselection.New_complex_ahp
             clause)
          (Some [ 1 ]) "E's order" );
    ( "E's backward unit simplification of processed clauses (loop.backward)",
      fun () ->
        (* FIFO (the sixth selection) takes p(f^5(a)) | q, whose q the active ~q cuts at once;
           ~p(f^5(X)) comes later and cuts the processed p(f^5(a)) to the empty clause
           (eliminate_unit_simplified_clauses). Without it the loop finds the same refutation by a
           generating resolution. The refutation stays kernel-checked. *)
        let problem =
          "cnf(s1,axiom,s1).\n\
           cnf(s2,axiom,s2).\n\
           cnf(s3,axiom,s3).\n\
           cnf(s4,axiom,s4).\n\
           cnf(c1,axiom,( p(f(f(f(f(f(a)))))) | q )).\n\
           cnf(c3,axiom,( ~ p(f(f(f(f(f(X)))))) )).\n\
           cnf(goal,negated_conjecture,( ~ q ))."
        in
        let t = Tptp.parse problem in
        let run loop =
          let config =
            {
              Scheduler.default_config with
              reference = false;
              loop = Some loop;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name "sat001";
                  goal_names = [ "goal" ];
                  limits = { Engine.default_limits with seconds = 30.; max_given = 2000 };
                };
            }
          in
          let r = Scheduler.run config t in
          (match r.certificate with
          | None -> ()
          | Some cert -> check (Result.is_ok (Kernel.check t cert)) "kernel rejected");
          r.engine
        in
        let on = run Heuristic.loop_member in
        let off = run { Heuristic.loop_member with backward = false } in
        check (off.metrics.backward_unit_cut = 0) "off: no backward unit cut";
        check
          (on.metrics.backward_unit_cut > 0)
          (Printf.sprintf "on: %d backward unit cuts" on.metrics.backward_unit_cut) );
    ( "E keeps the variants that presaturation makes (loop.presat_duplicates)",
      fun () ->
        (* f(a) = a rewrites p(f(a)) to p(a), a variant of the input p(a). E keeps such a copy
           (it subsumes with the processed clauses only, and a Passive variant waits for its
           selection), so presaturation drops no variant; without [presat_duplicates] the main
           loop's deviation ([duplicates] off) already drops the copy there. The problem is
           satisfiable and the main loop generates nothing. *)
        let problem =
          "cnf(c1,axiom,p(f(a))).\n\
           cnf(c2,axiom,p(a)).\n\
           cnf(e1,axiom,f(a) = a).\n\
           cnf(goal,negated_conjecture,~ q)."
        in
        let t = Tptp.parse problem in
        let run loop =
          let config =
            {
              Scheduler.default_config with
              reference = false;
              loop = Some loop;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name "sat001";
                  goal_names = [ "goal" ];
                  limits = { Engine.default_limits with seconds = 30.; max_given = 2000 };
                };
            }
          in
          let r = Scheduler.run config t in
          check (r.certificate = None) "a satisfiable problem has no refutation";
          check (not r.engine.presat_running) "presaturation ended";
          r.engine
        in
        let on = run Heuristic.loop_member in
        let off = run { Heuristic.loop_member with presat_duplicates = false } in
        check (on.metrics.duplicates = 0)
          (Printf.sprintf "on: %d variants dropped" on.metrics.duplicates);
        check (off.metrics.duplicates > 0) "off: presaturation drops the copy" );
    ( "E's canonical order decides which equational definitions are unfolded",
      fun () ->
        (* E tests each clause once in its canonical order: unfolding b first makes a's right side
           c^12(X), 21 heavier than a(X), so a stays; unfolding a first removes both. *)
        let fn f args = Fn (Original f, args) and x = V (0, 0) in
        let rec c n t = if n = 0 then t else fn "c" [ c (n - 1) t ] in
        let def_a = [ positive (E (fn "a" [ x ], fn "b" [ fn "b" [ x ] ])) ] in
        let def_b = [ positive (E (fn "b" [ x ], c 6 x)) ] in
        let use = [ positive (P ("p", [ fn "a" [ fn "k" [] ] ])) ] in
        let removed order =
          match Unfold.plan ~order ~limit:Unfold.default_limit [ def_a; def_b; use ] with
          | None -> []
          | Some plan -> List.sort compare (List.map fst plan.removed)
        in
        equal (removed [ 0; 1; 2 ]) [ 0; 1 ] "a first: both unfolded";
        equal (removed [ 1; 0; 2 ]) [ 1 ] "b first: a exceeds the limit" );
    ( "E's simultaneous paramodulation: every chain step is a kernel paramodulation and the result \
       is E's clause (ClauseSimParamodConstruct)",
      fun () ->
        (* Random into clauses built from a few subterms (so they repeat), and from clauses whose
           equation's side is one of them (so it unifies with several occurrences), sometimes with
           a side literal. Every paramodulant of the unordered calculus goes through the chain;
           every recorded intermediate and the last step must be their rules' kernel conclusions,
           and the result must be E's: sigma(C) and sigma(D) with every occurrence of the into
           subterm replaced. *)
        let rng = Random.State.make [| 20261119 |] in
        let pick a = a.(Random.State.int rng (Array.length a)) in
        let calc = Calculus.create (Term.create ()) in
        let step id clause = { id; clause = Clause.normalize clause; rule = Input (id, 0) } in
        let apply sigma =
          let rec go = function
            | V v as t -> ( match List.assoc_opt v sigma with Some u -> u | None -> t)
            | Fn (f, ts) -> Fn (f, List.map go ts)
          in
          go
        in
        let expected (from : step) (into : step) = function
          | Paramodulate (_, i, reverse, _, j, path, sigma) ->
              let xs = Clause.scope 1 from.clause and ys = Clause.scope 2 into.clause in
              let s = Clause.at (List.nth ys j) path in
              let rhs =
                match (List.nth xs i).atom with
                | E (a, b) -> if reverse then a else b
                | _ -> failwith "not an equation"
              in
              let rec replace t =
                if t = s then rhs
                else match t with V _ -> t | Fn (f, ts) -> Fn (f, List.map replace ts)
              in
              Clause.normalize
                (List.map
                   (Clause.map_literal (apply sigma))
                   (Clause.remove i xs @ List.map (Clause.map_literal replace) ys))
          | _ -> failwith "not a paramodulation"
        in
        let plain = ref 0 and chains = ref 0 and fallbacks = ref 0 and steps = ref 0 in
        for _ = 1 to 400 do
          let pool = Array.init 3 (fun _ -> random_term rng 2) in
          let term () =
            match Random.State.int rng 3 with
            | 0 -> pick pool
            | 1 -> fn "h" [ pick pool; pick pool ]
            | _ -> fn "f" [ pick pool ]
          in
          let literal () =
            let positive = Random.State.bool rng in
            match Random.State.int rng 3 with
            | 0 -> { positive; atom = P ("p", [ term (); term () ]) }
            | 1 -> { positive; atom = eq (term ()) (term ()) }
            | _ -> { positive; atom = P ("q", [ term () ]) }
          in
          let into = step 1 (List.init (1 + Random.State.int rng 3) (fun _ -> literal ())) in
          let from =
            step 0
              (positive (eq (pick pool) (random_term rng 1))
              :: (if Random.State.bool rng then [ literal () ] else []))
          in
          Calculus.paramodulate calc from into (fun clause rule ->
              let nodes = ref [ from; into ] in
              let record clause rule =
                let s = { id = List.length !nodes; clause = Clause.normalize clause; rule } in
                nodes := !nodes @ [ s ];
                s
              in
              match E_simparamod.chain ~record ~from ~into clause rule with
              | Plain ->
                  incr plain;
                  check
                    (Variant_index.variants (Clause.normalize clause) (expected from into rule))
                    "a plain paramodulant that is not E's"
              | Fallback k ->
                  incr fallbacks;
                  equal k 0 "a fallback after recording"
              | Simultaneous { clause = last; rule = last_rule; steps = k } ->
                  incr chains;
                  steps := !steps + k;
                  equal k (List.length !nodes - 2) "recorded intermediates";
                  check (k >= 1) "a chain without intermediates";
                  let derive rule = Kernel.derive ~inputs:[] ~steps:!nodes rule in
                  List.iter
                    (fun (s : step) ->
                      if s.id >= 2 then
                        equal (derive s.rule) (Ok s.clause)
                          "an intermediate is not its rule's conclusion")
                    !nodes;
                  equal (derive last_rule)
                    (Ok (Clause.normalize last))
                    "the last step is not its rule's conclusion";
                  check
                    (Variant_index.variants (Clause.normalize last) (expected from into rule))
                    "not E's simultaneous paramodulant")
        done;
        check (!chains >= 50)
          (Printf.sprintf "chains %d, plain %d, fallbacks %d" !chains !plain !fallbacks);
        check (!steps > !chains) "every chain had a single intermediate";
        (* p(f(X),X) | p(f(a),a) | q(f(X)) with f(a) = b at q(f(X)): sigma = {X -> a} makes
           p(f(X),X) equal to p(f(a),a), which E keeps unreplaced; starting the chain at q(f(X))
           would merge them, so it starts at p(f(X),X). *)
        let from = step 0 [ positive (eq (fn "f" [ c "a" ]) (c "b")) ] in
        let into =
          step 1
            [
              positive (P ("p", [ fn "f" [ x ]; x ]));
              positive (P ("p", [ fn "f" [ c "a" ]; c "a" ]));
              positive (P ("q", [ fn "f" [ x ] ]));
            ]
        in
        let results = ref [] in
        Calculus.paramodulate calc from into (fun clause rule ->
            let nodes = ref [ from; into ] in
            let record clause rule =
              let s = { id = List.length !nodes; clause = Clause.normalize clause; rule } in
              nodes := !nodes @ [ s ];
              s
            in
            match E_simparamod.chain ~record ~from ~into clause rule with
            | Simultaneous { clause = last; _ } -> results := Clause.normalize last :: !results
            | Plain -> ()
            | Fallback _ -> failwith "a feasible order exists");
        let sim =
          Clause.normalize
            [
              positive (P ("p", [ c "b"; c "a" ]));
              positive (P ("p", [ fn "f" [ c "a" ]; c "a" ]));
              positive (P ("q", [ c "b" ]));
            ]
        in
        equal (List.length !results) 2 "both occurrences of f(X) give the simultaneous clause";
        List.iter (fun r -> check (same r sim) "not E's clause") !results );
    ( "E's simultaneous paramodulation in the E-loop members (loop.sim_paramod)",
      fun () ->
        (* f(X) = g(X) | q(X) into p(f(a),h(f(a),f(b))) | r(f(a)) replaces the three f(a) at once
           (two proof-only intermediates); f(b) stays. h047 refutes with it, and without it. *)
        let refute loop text =
          let t = Tptp.parse text in
          let config =
            {
              Scheduler.default_config with
              reference = false;
              portfolio = Strategy.Workers [ Strategy.of_name "h047" ];
              slices = Some Slices.off;
              loop = Some loop;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name "h047";
                  goal_names = [ "goal" ];
                  limits = { Engine.default_limits with seconds = 30.; max_given = 2000 };
                };
            }
          in
          let r = Scheduler.run config t in
          (match r.certificate with
          | None -> ()
          | Some cert -> check (Result.is_ok (Kernel.check t cert)) "kernel rejected");
          (r.certificate <> None, r.engine)
        in
        let problem =
          "cnf(c1,axiom,( f(X) = g(X) | q(X) )).\n\
           cnf(c2,axiom,( p(f(a),h(f(a),f(b))) | r(f(a)) )).\n\
           cnf(c3,axiom,( ~ p(g(a),h(g(a),f(b))) )).\n\
           cnf(c4,axiom,( ~ r(g(a)) )).\n\
           cnf(goal,negated_conjecture,( ~ q(a) ))."
        in
        let refuted, on = refute Heuristic.loop_e problem in
        check refuted "no refutation with sim_paramod";
        equal on.metrics.sim_paramodulants 1 "simultaneous paramodulants";
        equal on.metrics.sim_steps 2 "intermediates";
        let refuted, off = refute { Heuristic.loop_e with sim_paramod = false } problem in
        check refuted "no refutation without sim_paramod";
        equal (off.metrics.sim_paramodulants + off.metrics.sim_steps) 0 "off: no chain";
        (* The given f(X) = g(X) | q(h^4(X)) is the from clause into the active p(f(a),f(a)): E
           makes one conclusion for the two positions of f(a), p(g(a),g(a)) | q(h^4(a)). *)
        let problem =
          "cnf(c2,axiom,( p(f(a),f(a)) )).\n\
           cnf(c1,axiom,( f(X) = g(X) | q(h(h(h(h(X))))) )).\n\
           cnf(c3,axiom,( ~ p(g(a),g(a)) | s(b) )).\n\
           cnf(c4,axiom,( ~ s(X) | ~ q(h(h(h(h(X))))) | ~ q(X) )).\n\
           cnf(c5,axiom,( q(a) )).\n\
           cnf(goal,negated_conjecture,( ~ s(b) | ~ q(h(h(h(h(b))))) )).\n\
           cnf(c6,axiom,( q(h(h(h(h(b))))) ))."
        in
        let _, on = refute Heuristic.loop_e problem in
        equal on.metrics.sim_merged 1 "one conclusion per from position, into clause and subterm";
        equal on.metrics.sim_paramodulants 1 "the simultaneous paramodulant";
        let _, off = refute { Heuristic.loop_e with sim_paramod = false } problem in
        equal off.metrics.sim_merged 0 "off: one conclusion per position" );
    ( "E makes a top-level overlap of two positive equations once (loop.top_once)",
      fun () ->
        (* f(X,X) = g(X) | p(X) and f(b,b) = h(b) | q overlap at the top of both equations. E makes
           the conclusion with the given as the from clause only (ComputeFromParamodulants skips the
           given's positive top positions); without top_once the given as the into clause makes it
           again. Both refute, kernel-checked. *)
        let problem =
          "cnf(c1,axiom,( f(X,X) = g(X) | p(X) )).\n\
           cnf(c2,axiom,( f(b,b) = h(b) | q )).\n\
           cnf(c3,axiom,( ~ p(b) )).\n\
           cnf(c4,axiom,( ~ q )).\n\
           cnf(goal,negated_conjecture,( g(b) != h(b) ))."
        in
        let run loop =
          let t = Tptp.parse problem in
          let config =
            {
              Scheduler.default_config with
              reference = false;
              portfolio = Strategy.Workers [ Strategy.of_name "h047" ];
              slices = Some Slices.off;
              loop = Some loop;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name "h047";
                  goal_names = [ "goal" ];
                  limits = { Engine.default_limits with seconds = 30.; max_given = 2000 };
                };
            }
          in
          let r = Scheduler.run config t in
          (match r.certificate with
          | None -> failwith "no refutation"
          | Some cert -> check (Result.is_ok (Kernel.check t cert)) "kernel rejected");
          r.engine.metrics
        in
        equal (run Heuristic.loop_e).top_skipped 1 "the given's top position is skipped";
        equal (run { Heuristic.loop_e with top_once = false }).top_skipped 0 "off: made twice" );
    ( "E's equational unit subsumption, forward and backward (loop.eqn_subsume)",
      fun () ->
        (* f(X,Y) = f(Y,X) subsumes g(f(X,a)) = g(f(a,X)) | q(X) below the top (E's
           eqn_subsumes_termpair); FullRewrite cannot rewrite it (f(X,a) and f(a,X) are
           incomparable), ordinary subsumption does not see it. Forward: the unit is active when the
           clause is selected. Backward: the unit (after the cut of its s(..) literal) comes after
           the active g(f(X,a)) = g(f(a,X)). Both problems are satisfiable. *)
        let run loop text =
          let t = Tptp.parse text in
          let config =
            {
              Scheduler.default_config with
              reference = false;
              portfolio = Strategy.Workers [ Strategy.of_name "h047" ];
              slices = Some Slices.off;
              loop = Some loop;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name "h047";
                  goal_names = [ "goal" ];
                  limits = { Engine.default_limits with seconds = 30.; max_given = 2000 };
                };
            }
          in
          let r = Scheduler.run config t in
          check (r.certificate = None) "a satisfiable problem has no refutation";
          r.engine.metrics
        in
        let forward =
          "cnf(comm,axiom,( f(X,Y) = f(Y,X) )).\n\
           cnf(c1,axiom,( g(f(X,a)) = g(f(a,X)) | q(X) )).\n\
           cnf(c2,axiom,( ~ q(b) | r )).\n\
           cnf(goal,negated_conjecture,( ~ r ))."
        in
        let on = run Heuristic.loop_e forward in
        equal on.eqn_subsumed 1 "forward: the selected clause is subsumed";
        let off = run { Heuristic.loop_e with eqn_subsume = false } forward in
        equal (off.eqn_subsumed + off.eqn_backward) 0 "off: no equational subsumption";
        let backward =
          "cnf(c1,axiom,( g(f(X,a)) = g(f(a,X)) )).\n\
           cnf(comm,axiom,( f(X,Y) = f(Y,X) | s(k(k(k(k(a))))) )).\n\
           cnf(goal,negated_conjecture,( ~ s(k(k(k(k(a))))) ))."
        in
        let on = run Heuristic.loop_e backward in
        equal on.eqn_backward 1 "backward: the active clause is subsumed";
        let off = run { Heuristic.loop_e with eqn_subsume = false } backward in
        equal off.eqn_backward 0 "off: kept" );
    ( "E's orphan deletion keeps the refutations of two minimal cases",
      fun () ->
        (* Every complete member that deletes orphans, and the DISCOUNT loop that deletes orphans
           without [duplicates], refute two minimal cases found by completeness fuzzing, where
           orphan deletion together with duplicate deletion once lost the refutation. *)
        let refutes ?loop name text =
          let t = Tptp.parse text in
          (* The member alone: the balanced single worker would share its time with e208's lane,
             which refutes both cases on the ported loop. *)
          let config =
            {
              Scheduler.default_config with
              reference = false;
              portfolio = Strategy.Workers [ Strategy.of_name name ];
              slices = Some Slices.off;
              loop;
              engine =
                {
                  Engine.default_config with
                  strategy = Strategy.of_name name;
                  goal_names = [ "goal" ];
                  limits = { Engine.default_limits with seconds = 30.; max_given = 20000 };
                };
            }
          in
          let r = Scheduler.run config t in
          match r.certificate with
          | None -> failwith (name ^ ": " ^ r.reason)
          | Some cert ->
              check (Result.is_ok (Kernel.check t cert)) (name ^ ": kernel rejected");
              r.engine
        in
        (* (1) X = a enters Passive as a conclusion of the two input clauses that the next given,
           a = f(X), backward-rewrites. Their replacements, X = a again, are the FullRewrite target,
           so the duplicate check dropped them for the Passive X = a, which was then deleted as an
           orphan: x1276 exhausted Passive after 5 given. The Passive clause now keeps their
           standing. *)
        let absorbed =
          "cnf(c1,axiom,(~p(h(g(Y,X))))).\n\
           cnf(c4,axiom,(X = f(f(X)))).\n\
           cnf(c7,axiom,(X = f(a))).\n\
           cnf(c9,axiom,(p(g(X,a)) | a != g(h(X),b)))."
        in
        (* (2) c = a backward-rewrites two active clauses whose own premises were already retired.
           Their replacements inherited those premises and were deleted as orphans, so h047, x1276,
           s4d, c01 and c41 exhausted Passive. E's copy of a backward-simplified clause comes from
           no generating inference and is never an orphan; neither is the replacement now. *)
        let copied =
          "cnf(c0,axiom,(~p(X) | k(b))).\n\
           cnf(c1,axiom,(p(X) | ~k(b))).\n\
           cnf(c2,axiom,(c != g(a,b) | b = h(h(b)))).\n\
           cnf(c3,axiom,(b = f(h(a)) | f(a) = b)).\n\
           cnf(c4,axiom,(h(c) = f(Z))).\n\
           cnf(c5,axiom,(h(a) = c | c = f(g(a,a)))).\n\
           cnf(c6,axiom,(g(f(Z),h(X)) != f(h(Z)) | f(g(Z,X)) != f(b))).\n\
           cnf(c7,axiom,(g(f(X),f(X)) = X | f(f(X)) = a)).\n\
           cnf(c8,axiom,(c != h(f(a)) | h(g(a,c)) = a)).\n\
           cnf(c9,axiom,(c != c | b = c)).\n\
           cnf(goal,negated_conjecture,(f(h(b)) != h(g(b,a)) | f(f(c)) != b))."
        in
        let deleting =
          List.filter
            (fun (h : Heuristic.t) ->
              h.loop.discount && h.loop.orphans && h.sine_filter = None && h.vampire = None)
            Heuristic.named
          |> List.map (fun (h : Heuristic.t) -> h.name)
        in
        List.iter
          (fun name -> check (List.mem name deleting) (name ^ " deletes orphans"))
          [ "h047"; "x1276"; "x1276rg"; "c18sos"; "c18c"; "b07c"; "s4d"; "c01"; "c41" ];
        List.iter
          (fun name ->
            ignore (refutes name absorbed);
            ignore (refutes name copied))
          deleting;
        (* The orphan deletion itself still runs: X = Y, the conclusion of the two retired input
           clauses, is still dropped as an orphan. *)
        check ((refutes "x1276" absorbed).metrics.orphans > 0) "x1276 dropped no orphan";
        (* Without [duplicates] the emission check drops the repeats instead. *)
        let emission = { Heuristic.loop_ported with discount = true; orphans = true } in
        ignore (refutes ~loop:emission "x1276" absorbed);
        ignore (refutes ~loop:emission "h047" copied) );
    ( "E components: SelectCQIPrecWNTNp, occurrence keys, selmax and precrank20",
      fun () ->
        let pkey name arity = (Ordering.Predicate name, arity) in
        let table = Hashtbl.create 8 in
        List.iter
          (fun (k, r) -> Hashtbl.replace table k (r, 1))
          [ (fkey "f" 1, 1); (pkey "p" 1, 3); (pkey "q" 1, 5); (pkey "r" 1, 2) ];
        let order = installed ~unified:true table in
        let select = Eselection.select ~order Eselection.Cq_iprec_w_nt_np in
        check
          (select
             [
               negative (P ("p", [ fn "f" [ x ] ]));
               negative (P ("q", [ fn "f" [ x ] ]));
               positive (P ("r", [ x ]));
             ]
          = Some [ 1 ])
          "the head greatest in the precedence (q) is selected";
        (* E weighs a variable lterm 0 and a head -prec_weight: any head of a positive rank comes
           before a variable lterm, which comes before an unknown (rank 0) head only alphabetically. *)
        check
          (select [ negative (P ("q", [ fn "f" [ x ] ])); negative (eq x (fn "f" [ y ])) ]
          = Some [ 0 ])
          "a ranked head comes before a variable lterm";
        check
          (select [ negative (P ("q", [ x ])); positive (P ("r", [ x ])) ] = None)
          "a type literal P(X) is never selected";
        (* Occurrence keys: a symbol of the negated conjecture only rises above the rest. *)
        (* Frequencies f 3, k 2, a 1, b 1: invfreq puts b (least frequent, seen last) on top. *)
        let clauses =
          [
            [ positive (eq (fn "f" [ c "a" ]) (c "b")) ];
            [ negative (eq (fn "f" [ c "k" ]) (fn "f" [ c "k" ])) ];
          ]
        in
        let conjecture key = List.mem key [ fkey "k" 0; fkey "f" 1 ] in
        let axiom key = List.mem key [ fkey "f" 1; fkey "a" 0; fkey "b" 0 ] in
        let kbo precedence weights =
          {
            Eorder.ordering = Kbo;
            precedence;
            weights;
            const_weight = 1;
            e_signature = false;
            e_ranks = false;
          }
        in
        let plain, _ = Eorder.table ~conjecture ~axiom (kbo Invfreq Unit_weights) clauses in
        let modified, _ =
          Eorder.table ~conjecture ~axiom
            (kbo
               (Occurrence (Invfreq, { conj_only = 10; conj_axiom = 0; axiom_only = 0 }))
               Unit_weights)
            clauses
        in
        let top t =
          Hashtbl.fold
            (fun k (r, _) (bk, br) -> if r > br then (k, r) else (bk, br))
            t
            (fkey "?" 0, -1)
          |> fst
        in
        check (top plain = fkey "b" 0) "invfreq alone puts the least frequent symbol on top";
        check (top modified = fkey "k" 0) "conj_only_mod puts the conjecture-only constant on top";
        (* selmax: every symbol 1, the greatest of the precedence (unary_first: f) 0. *)
        let selmax, _ = Eorder.table (kbo Unary_first Selmax) clauses in
        check (weight selmax (fkey "f" 1) = 0) "selmax: the greatest (unary) symbol weighs 0";
        check (weight selmax (fkey "a" 0) = 1 && weight selmax (fkey "b" 0) = 1) "selmax: others 1";
        (* precrank20: weights 1..20, non-decreasing in the precedence. *)
        let many = [ List.init 30 (fun i -> positive (P (Printf.sprintf "p%02d" i, [ c "a" ]))) ] in
        let pr, _ = Eorder.table (kbo Invfreq Precrank20) many in
        let ws =
          Hashtbl.fold (fun _ (r, w) acc -> (r, w) :: acc) pr []
          |> List.sort compare |> List.map snd
        in
        check (List.for_all (fun w -> w >= 1 && w <= 20) ws) "precrank20 weighs 1..20";
        check
          (fst (List.fold_left (fun (ok, last) w -> (ok && w >= last, w)) (true, 0) ws))
          "precrank20 is monotone in the precedence";
        check (List.hd ws = 1 && List.nth ws (List.length ws - 1) = 20) "precrank20 spans 1..20" );
    ( "E relevance levels, RelevanceLevelWeight2 and ConjectureGeneralSymbolWeight arithmetic",
      fun () ->
        let p a = P ("p", [ a ]) and q a = P ("q", [ a ]) in
        let goals = [ [ negative (p (c "a")) ] ] in
        let others =
          [
            [ negative (p x); positive (q x) ];
            [ positive (q (c "b")); positive (P ("r", [ c "c" ])) ];
            [ positive (P ("s", [ c "d" ])) ];
          ]
        in
        let rel = Evaluation.relevance_levels ~goals ~others in
        let level k = rel.symbol_level k in
        let pk name = (Ordering.Predicate name, 1) in
        check (level (pk "p") = Some 1 && level (fkey "a" 0) = Some 1) "level 1: the goal symbols";
        check (level (pk "q") = Some 2) "level 2: symbols of clauses sharing a level-1 symbol";
        check (level (fkey "b" 0) = Some 3 && level (pk "r") = Some 3) "level 3";
        check (level (pk "s") = None && rel.max_level = 4) "s unreached, one past the last level";
        let facts =
          {
            Evaluation.initial = false;
            sos = false;
            processed = false;
            conjecture = Some (Evaluation.conjecture_symbols goals);
            age = 1;
            level = 0;
            relevance = Some rel;
          }
        in
        let relevance =
          {
            Evaluation.count = 1;
            priority = Const_prio;
            weight =
              Relevance2
                {
                  const = 0.;
                  lin = 2.;
                  square = 1.;
                  penalty = 2;
                  fweight = 100;
                  cweight = 100;
                  pweight = 100;
                  vweight = 400;
                  max_term = 1.5;
                  max_literal = 1.5;
                  positive = 1.;
                };
          }
        in
        (* q(b) = $true: q level 2 -> 100*(2*2+4) = 800, b level 3 -> 100*(6+9) = 1500, $true
           level 1 -> 300; oriented, so 300 + (800+1500)*1.5 = 3750, maximal *1.5 = 5625. *)
        let w = snd (Evaluation.evaluate [ relevance ] facts [ positive (q (c "b")) ]).(0) in
        check (Float.abs (w -. 5625.) < 1e-6) (Printf.sprintf "RelevanceLevelWeight2: %g" w);
        (* s(d) unreached: penalty 2 + max_level 4 = 6 -> 100*(12+36) = 4800 each; 300 +
           9600*1.5 = 14700, *1.5 = 22050. *)
        let w =
          snd (Evaluation.evaluate [ relevance ] facts [ positive (P ("s", [ c "d" ])) ]).(0)
        in
        check (Float.abs (w -. 22050.) < 1e-6) (Printf.sprintf "unreached symbols: %g" w);
        let general =
          {
            Evaluation.count = 1;
            priority = Const_prio;
            weight =
              Conj_general
                {
                  fweight = 200;
                  cweight = 100;
                  pweight = 200;
                  conj_fweight = 50;
                  conj_cweight = 50;
                  conj_pweight = 1;
                  vweight = 100;
                  max_term = 1.5;
                  max_literal = 1.5;
                  positive = 1.;
                };
          }
        in
        (* p(a) with p, a and $true conjecture symbols: rterm $true 1 + lterm (1 + 50) * 1.5 =
           77.5, maximal * 1.5 = 116.25; q(b): 1 + (200 + 100) * 1.5 = 451, * 1.5 = 676.5. *)
        let w = snd (Evaluation.evaluate [ general ] facts [ positive (p (c "a")) ]).(0) in
        check (Float.abs (w -. 116.25) < 1e-6) (Printf.sprintf "conjecture symbols: %g" w);
        let w = snd (Evaluation.evaluate [ general ] facts [ positive (q (c "b")) ]).(0) in
        check (Float.abs (w -. 676.5) < 1e-6) (Printf.sprintf "other symbols: %g" w) );
    ( "a SInE-filtered member drops the unreached axioms and still finds a checked refutation",
      fun () ->
        (* g/h/k never meet the conjecture's symbols: SInE drops c4 and c5, the proof needs c1-c3. *)
        let problem =
          "cnf(c1,axiom,(p(X) | ~q(X))). cnf(c2,axiom,(q(a))). cnf(c3,axiom,(~p(X) | r(X))).\n\
           cnf(c4,axiom,(g(h(X)) = k(X))). cnf(c5,axiom,(g(k(X)) = h(X))).\n\
           cnf(c6,negated_conjecture,(~r(a)))."
        in
        let t = Tptp.parse problem in
        let config =
          {
            Scheduler.default_config with
            reference = false;
            portfolio = Strategy.Workers [ Strategy.of_name "c18csl" ];
            engine =
              {
                Engine.default_config with
                goal_names = [ "c6" ];
                limits = { Engine.default_limits with seconds = 20. };
              };
          }
        in
        let r = Scheduler.portfolio ~workers:1 config (fun () -> Theory.copy t) in
        match r.certificate with
        | None -> failwith ("no refutation: " ^ r.reason)
        | Some cert ->
            check (Result.is_ok (Kernel.check t cert)) "kernel rejected";
            let used =
              List.filter_map
                (fun (s : step) -> match s.rule with Input (a, _) -> Some a | _ -> None)
                cert.steps
            in
            check (used <> []) "the refutation uses input clauses" );
  ]

let () = run (if Array.mem "--eval" Sys.argv then eval_tests else tests)
