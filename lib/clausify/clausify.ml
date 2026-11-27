open Wire

exception Limit

type nnf = Lit of literal | And of nnf list | Or of nnf list

let run ?(limit = 10000) ?(mode = Hybrid) ?(guard = fun () -> ()) (ax : axiom) =
  if limit < 0 then invalid_arg "negative CNF limit";
  let next_var = ref 0 and next_sk = ref 0 in
  let rec term env = function
    | B i -> ( try List.nth env i with Failure _ -> invalid_arg "Clausify: dangling index")
    | F _ -> invalid_arg "Clausify: source axiom not closed"
    | App (s, ts) -> Fn (Intern.original s, List.map (term env) ts)
  in
  let rec nnf positive env universals f =
    guard ();
    match f with
    | Top -> if positive then And [] else Or []
    | Bot -> if positive then Or [] else And []
    | Pred (s, ts) -> Lit { positive; atom = P (Intern.name s, List.map (term env) ts) }
    | Eq (x, y) -> Lit { positive; atom = E (term env x, term env y) }
    | Neg f -> nnf (not positive) env universals f
    | Conj fs ->
        let fs = List.map (nnf positive env universals) fs in
        if positive then And fs else Or fs
    | Disj fs ->
        let fs = List.map (nnf positive env universals) fs in
        if positive then Or fs else And fs
    | All f -> quant positive positive env universals f
    | Ex f -> quant (not positive) positive env universals f
  and quant universal positive env universals f =
    if universal then (
      let v = V (0, !next_var) in
      incr next_var;
      nnf positive (v :: env) (universals @ [ v ]) f)
    else
      let sk = Fn (Skolem (ax.axiom_id, !next_sk), universals) in
      incr next_sk;
      nnf positive (sk :: env) universals f
  in
  let product xs ys =
    if ys <> [] && List.length xs > limit / List.length ys then raise Limit;
    List.concat_map (fun x -> List.map (fun y -> x @ y) ys) xs
  in
  let rec cnf f =
    guard ();
    match f with
    | Lit l -> [ [ l ] ]
    | And xs ->
        let cs = List.concat_map cnf xs in
        if List.length cs > limit then raise Limit;
        cs
    | Or xs -> List.fold_left (fun cs f -> product cs (cnf f)) [ [] ] xs
  in
  let matrix = nnf true [] [] ax.formula in
  let cap = hybrid_cnf_limit + 1 in
  let rec estimate = function
    | Lit _ -> 1
    | And fs -> List.fold_left (fun n f -> min cap (n + estimate f)) 0 fs
    | Or fs -> List.fold_left (fun n f -> min cap (n * estimate f)) 1 fs
  in
  let define () =
    let next = ref 0 and clauses = ref [] and count = ref 0 in
    let add c =
      guard ();
      incr count;
      if !count > limit then raise Limit;
      clauses := c :: !clauses
    in
    let neg l = { l with positive = not l.positive } in
    let rec term_variables acc = function
      | V v -> v :: acc
      | Fn (_, ts) -> List.fold_left term_variables acc ts
    in
    let rec name = function
      | Lit l -> l
      | (And fs | Or fs) as f ->
          let children = List.map name fs in
          let vars =
            List.fold_left
              (fun acc l -> List.fold_left term_variables acc (Clause.atom_terms l.atom))
              [] children
            |> List.sort_uniq compare
          in
          let z =
            { positive = true; atom = D ((ax.axiom_id, !next), List.map (fun v -> V v) vars) }
          in
          incr next;
          (match f with
          | And _ ->
              List.iter (fun l -> add [ neg z; l ]) children;
              add (z :: List.map neg children)
          | Or _ ->
              add (neg z :: children);
              List.iter (fun l -> add [ z; neg l ]) children
          | Lit _ -> assert false);
          z
    in
    let root = name matrix in
    add [ root ];
    List.rev !clauses
  in
  (match mode with
    | Distributive -> cnf matrix
    | Hybrid when estimate matrix <= hybrid_cnf_limit -> cnf matrix
    | Definitional | Hybrid -> define ())
  |> List.map Clause.normalize
