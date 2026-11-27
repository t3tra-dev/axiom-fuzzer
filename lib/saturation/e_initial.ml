open Wire
(** E 3.5.9's evaluation order of the initial clauses (CONTROL/cco_proofproc.c ProofStateInit): the
    axioms are sorted by clause structure (ClauseSetCanonize, CLAUSES/ccl_clausefunc.c:400:
    ClauseCanonize, then ClauseStructWeightLexCompare, ccl_clauses.c:671), reweighted with the
    "Uniq" heuristic (HEURISTICS/che_clauseweight.c UniqWeightCompute) and evaluated by the search
    heuristic in increasing UniqWeight, ties in that sorted order. E breaks every later tie between
    equal evaluations by evaluation order (ccl_neweval.c EvalCompare), so this order decides which
    of two equally weighted initial clauses E selects first. A search-order choice only: every
    clause is still an ordinary input step. *)

(* Symbol codes: E's signature numbers symbols in their order of first appearance in the input
   (after its internal symbols), predicate and function symbols together; $true, the right side
   of a predicate literal, has code 1 and is the least term. Variables have negative codes in
   order of appearance in their clause. *)
type codes = { symbol : string -> int; truth : int; name : int -> string option }

(* E's input as its parser reads it, a search-order hint from the problem text ([of_text]): the
   symbol codes in E's parse order, and the literals of every cnf clause as written. *)
type tterm = TVar of string | TApp of string * tterm list

type tlit = { tpositive : bool; tequation : bool; tleft : tterm; tright : tterm option }
(** One literal of a cnf clause as written: an equation [tleft = tright] (or [!=]), or the predicate
    atom [tleft] ([tright = None]). *)

type text = { symbols : (string, int) Hashtbl.t; clauses : (string, tlit list) Hashtbl.t }
(** [symbols]: E's code of every symbol of the text; [clauses]: the cnf clauses by formula name. *)

(** E's symbol codes and cnf clauses from the problem text: E's parser enters a term's argument
    symbols into the signature before its head symbol (TERMS/cte_termbanks.c TBTermParseReal), an
    equation's left side before its right side and the literals of a clause left to right
    (ClauseParse), formulas in input order, predicate and function symbols in one signature after
    E's 22 internal symbols. [None] for text outside the cnf/fof subset this reads (the engine then
    numbers the symbols from its clauses, as before). *)
let of_text text =
  let n = String.length text in
  let pos = ref 0 in
  let symbols = Hashtbl.create 64 and clauses = Hashtbl.create 64 in
  let note name =
    if not (Hashtbl.mem symbols name) then Hashtbl.replace symbols name (Hashtbl.length symbols + 23)
  in
  let exception Unsupported in
  let is_alnum c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '$'
  in
  let rec skip () =
    if !pos < n then
      match text.[!pos] with
      | ' ' | '\t' | '\n' | '\r' ->
          incr pos;
          skip ()
      | '%' ->
          while !pos < n && text.[!pos] <> '\n' do
            incr pos
          done;
          skip ()
      | '/' when !pos + 1 < n && text.[!pos + 1] = '*' ->
          pos := !pos + 2;
          while !pos + 1 < n && not (text.[!pos] = '*' && text.[!pos + 1] = '/') do
            incr pos
          done;
          pos := !pos + 2;
          skip ()
      | _ -> ()
  in
  let peek () =
    skip ();
    if !pos < n then Some text.[!pos] else None
  in
  let name () =
    skip ();
    if !pos < n && text.[!pos] = '\'' then (
      let start = !pos + 1 in
      incr pos;
      while !pos < n && text.[!pos] <> '\'' do
        incr pos
      done;
      if !pos >= n then raise Unsupported;
      incr pos;
      String.sub text start (!pos - start - 1))
    else
      let start = !pos in
      while !pos < n && is_alnum text.[!pos] do
        incr pos
      done;
      if !pos = start then raise Unsupported;
      String.sub text start (!pos - start)
  in
  let expect c = if peek () = Some c then incr pos else raise Unsupported in
  let accept s =
    skip ();
    let k = String.length s in
    if !pos + k <= n && String.sub text !pos k = s then (
      pos := !pos + k;
      true)
    else false
  in
  let variable s = s <> "" && ((s.[0] >= 'A' && s.[0] <= 'Z') || s.[0] = '_') in
  (* A term, its symbols entered after its arguments'. *)
  let rec term () =
    let s = name () in
    if peek () = Some '(' then (
      incr pos;
      let rec more acc =
        let t = term () in
        if peek () = Some ',' then (
          incr pos;
          more (t :: acc))
        else (
          expect ')';
          List.rev (t :: acc))
      in
      let args = more [] in
      if s.[0] <> '$' then note s;
      TApp (s, args))
    else if variable s then TVar s
    else (
      if s.[0] <> '$' then note s;
      TApp (s, []))
  in
  let equality () =
    if accept "!=" then Some false
    else (
      skip ();
      if !pos < n && text.[!pos] = '=' && (!pos + 1 >= n || text.[!pos + 1] <> '>') then (
        incr pos;
        Some true)
      else None)
  in
  let atom positive =
    let t = term () in
    match equality () with
    | Some sign ->
        let u = term () in
        { tpositive = positive = sign; tequation = true; tleft = t; tright = Some u }
    | None -> { tpositive = positive; tequation = false; tleft = t; tright = None }
  in
  (* A cnf clause: literals separated by '|', each optionally negated or parenthesised. *)
  let rec literal () =
    match peek () with
    | Some '~' ->
        incr pos;
        let l = literal () in
        { l with tpositive = not l.tpositive }
    | Some '(' ->
        incr pos;
        let l = literal () in
        expect ')';
        l
    | _ -> atom true
  in
  let rec disjunction acc =
    let l = literal () in
    if accept "|" then disjunction (l :: acc) else List.rev (l :: acc)
  in
  let rec cnf_body () =
    (* "( l1 | ... )", "l1 | ...", or nested parentheses around the whole disjunction *)
    let save = !pos in
    match peek () with
    | Some '(' -> (
        incr pos;
        match
          let lits = cnf_body () in
          expect ')';
          lits
        with
        | lits when peek () <> Some '|' -> lits
        | _ ->
            pos := save;
            disjunction []
        | exception Unsupported ->
            pos := save;
            disjunction [])
    | _ -> disjunction []
  in
  let rec formula () =
    unit_formula ();
    let rec binary () =
      if
        accept "<=>" || accept "<~>" || accept "=>" || accept "<=" || accept "~|" || accept "~&"
        || accept "|" || accept "&"
      then (
        unit_formula ();
        binary ())
    in
    binary ()
  and unit_formula () =
    match peek () with
    | Some '(' ->
        incr pos;
        formula ();
        expect ')'
    | Some '~' ->
        incr pos;
        unit_formula ()
    | Some ('!' | '?') ->
        incr pos;
        expect '[';
        let rec vars () =
          ignore (name ());
          if peek () = Some ',' then (
            incr pos;
            vars ())
        in
        vars ();
        expect ']';
        expect ':';
        unit_formula ()
    | _ -> ignore (atom true)
  in
  try
    let rec entries () =
      match peek () with
      | None -> ()
      | Some _ ->
          let language = name () in
          expect '(';
          let formula_name = name () in
          expect ',';
          ignore (name ());
          expect ',';
          (match language with
          | "cnf" -> Hashtbl.replace clauses formula_name (cnf_body ())
          | "fof" -> formula ()
          | _ -> raise Unsupported);
          expect ')';
          expect '.';
          entries ()
    in
    entries ();
    Some { symbols; clauses }
  with Unsupported | Invalid_argument _ -> None

let codes ?text (clauses : clause list) =
  let table = Hashtbl.create 64 in
  let next =
    ref
      (match text with
      | Some t ->
          Hashtbl.iter (Hashtbl.replace table) t.symbols;
          23 + Hashtbl.length t.symbols
      | None -> 23)
  in
  let note name =
    if not (Hashtbl.mem table name) then (
      Hashtbl.replace table name !next;
      incr next)
  in
  let symbol_name = function Original f -> f | Skolem (a, i) -> Printf.sprintf "sk%d_%d" a i in
  let rec term = function
    | V _ -> ()
    | Fn (f, ts) ->
        note (symbol_name f);
        List.iter term ts
  in
  List.iter
    (List.iter (fun l ->
         match l.atom with
         | E (s, t) ->
             term s;
             term t
         | P (p, ts) ->
             note p;
             List.iter term ts
         | D ((a, i), ts) ->
             note (Printf.sprintf "def%d_%d" a i);
             List.iter term ts))
    clauses;
  let names = Hashtbl.create (Hashtbl.length table) in
  Hashtbl.iter (fun name code -> Hashtbl.replace names code name) table;
  {
    symbol = (fun name -> Option.value ~default:max_int (Hashtbl.find_opt table name));
    truth = 1;
    name = Hashtbl.find_opt names;
  }

(* E's view of a literal: lterm = rterm, a predicate atom P(ts) = $true. *)
type eterm = Var of int | App of int * eterm list
type elit = { positive : bool; equation : bool; lterm : eterm; rterm : eterm }

let symbol_name = function Original f -> f | Skolem (a, i) -> Printf.sprintf "sk%d_%d" a i

let view codes (c : clause) =
  let vars = Hashtbl.create 8 in
  let var v =
    match Hashtbl.find_opt vars v with
    | Some k -> k
    | None ->
        let k = -(2 * (Hashtbl.length vars + 1)) in
        Hashtbl.replace vars v k;
        k
  in
  let rec term = function
    | V v -> Var (var v)
    | Fn (f, ts) -> App (codes.symbol (symbol_name f), List.map term ts)
  in
  List.map
    (fun (l : literal) ->
      match l.atom with
      | E (s, t) ->
          let s = term s in
          let t = term t in
          { positive = l.positive; equation = true; lterm = s; rterm = t }
      | P (p, ts) ->
          {
            positive = l.positive;
            equation = false;
            lterm = App (codes.symbol p, List.map term ts);
            rterm = App (codes.truth, []);
          }
      | D ((a, i), ts) ->
          {
            positive = l.positive;
            equation = false;
            lterm = App (codes.symbol (Printf.sprintf "def%d_%d" a i), List.map term ts);
            rterm = App (codes.truth, []);
          })
    c

(* E's view of a cnf clause as written: E numbers its variables in order of first appearance
   (the parser's VarBankExtNameAssertAlloc after VarBankClearExtNames, ccl_clauses.c ClauseParse),
   an equation keeps its written sides until EqnCanonize. *)
let text_view codes (lits : tlit list) =
  let vars = Hashtbl.create 8 in
  let rec term = function
    | TVar v -> (
        match Hashtbl.find_opt vars v with
        | Some k -> Var k
        | None ->
            let k = -(2 * (Hashtbl.length vars + 1)) in
            Hashtbl.replace vars v k;
            Var k)
    | TApp (f, ts) ->
        let code = codes.symbol f in
        App (code, List.map term ts)
  in
  List.map
    (fun l ->
      let lterm = term l.tleft in
      let rterm = match l.tright with Some t -> term t | None -> App (codes.truth, []) in
      { positive = l.tpositive; equation = l.tequation; lterm; rterm })
    lits

(* Whether a cnf clause as written is [c] up to literal order, equation symmetry and variable
   names: the same multiset of literals with variables anonymized. A clause that our
   clausification or preprocessing changed keeps the view of [c]. *)
let matches (c : clause) (lits : tlit list) =
  let rec ours = function
    | V _ -> "_"
    | Fn (f, []) -> symbol_name f
    | Fn (f, ts) -> symbol_name f ^ "(" ^ String.concat "," (List.map ours ts) ^ ")"
  in
  let rec theirs = function
    | TVar _ -> "_"
    | TApp (f, []) -> f
    | TApp (f, ts) -> f ^ "(" ^ String.concat "," (List.map theirs ts) ^ ")"
  in
  let pair sign a b =
    let a, b = if compare a b <= 0 then (a, b) else (b, a) in
    sign ^ a ^ "=" ^ b
  in
  let our_keys =
    List.map
      (fun (l : literal) ->
        let sign = if l.positive then "+" else "-" in
        match l.atom with
        | E (a, b) -> Some (pair sign (ours a) (ours b))
        | P (p, ts) -> Some (sign ^ ours (Fn (Original p, ts)))
        | D _ -> None)
      c
  in
  let their_keys =
    List.map
      (fun l ->
        let sign = if l.tpositive then "+" else "-" in
        match l.tright with
        | Some r when l.tequation -> Some (pair sign (theirs l.tleft) (theirs r))
        | _ -> Some (sign ^ theirs l.tleft))
      lits
  in
  List.length c = List.length lits
  && List.for_all Option.is_some our_keys
  && List.sort compare our_keys = List.sort compare their_keys

(* TermStandardWeight: function symbols 2, variables 1. *)
let rec standard_weight = function
  | Var _ -> 1
  | App (_, ts) -> List.fold_left (fun n t -> n + standard_weight t) 2 ts

let is_truth codes = function App (f, []) -> f = codes.truth | _ -> false

(* TermStructWeightCompare (TERMS/cte_termfunc.c:1690). *)
let rec struct_compare codes a b =
  match (is_truth codes a, is_truth codes b) with
  | true, true -> 0
  | true, false -> -1
  | false, true -> 1
  | false, false -> (
      let w = compare (standard_weight a) (standard_weight b) in
      if w <> 0 then w
      else
        match (a, b) with
        | Var _, _ | _, Var _ -> 0
        | App (_, xs), App (_, ys) ->
            let k = compare (List.length xs) (List.length ys) in
            if k <> 0 then k
            else
              List.fold_left2
                (fun acc x y -> if acc <> 0 then acc else struct_compare codes x y)
                0 xs ys)

(* TermLexCompare (cte_termfunc.c:1773): codes, then arguments left to right. *)
let rec lex_compare a b =
  let code = function Var k -> k | App (f, _) -> f in
  let c = compare (code a) (code b) in
  if c <> 0 then c
  else
    match (a, b) with
    | App (_, xs), App (_, ys) when List.length xs = List.length ys ->
        List.fold_left2 (fun acc x y -> if acc <> 0 then acc else lex_compare x y) 0 xs ys
    | _ -> 0

(* EqnCanonize: equal structure, the lexically greater side first. *)
let canonize codes l =
  if struct_compare codes l.lterm l.rterm = 0 && lex_compare l.lterm l.rterm < 0 then
    { l with lterm = l.rterm; rterm = l.lterm }
  else l

let literal_weight l = standard_weight l.lterm + standard_weight l.rterm

(* EqnStructWeightCompare (ccl_eqn.c:1916), then EqnStructWeightLexCompare's lexical part. *)
let literal_struct_compare codes a b =
  if a.positive && not b.positive then -1
  else if b.positive && not a.positive then 1
  else if a.equation && not b.equation then -1
  else if b.equation && not a.equation then 1
  else
    let w = compare (literal_weight a) (literal_weight b) in
    if w <> 0 then w
    else
      let s = struct_compare codes a.lterm b.lterm in
      if s <> 0 then s else struct_compare codes a.rterm b.rterm

let literal_compare codes a b =
  let s = literal_struct_compare codes a b in
  if s <> 0 then s
  else
    let l = lex_compare a.lterm b.lterm in
    if l <> 0 then l else lex_compare a.rterm b.rterm

(* ClauseStructWeightLexCompare: sign class, literal counts, weight, literals structurally, then
   lexically; the caller breaks the last ties by input position (E's clause ident). *)
let clause_compare codes a b =
  let cls lits =
    if List.for_all (fun l -> l.positive) lits then 0
    else if List.for_all (fun l -> not l.positive) lits then 2
    else 1
  in
  let count p lits = List.length (List.filter p lits) in
  let weight lits = List.fold_left (fun n l -> n + literal_weight l) 0 lits in
  let c = compare (cls a) (cls b) in
  if c <> 0 then c
  else
    let c = compare (count (fun l -> not l.positive) a) (count (fun l -> not l.positive) b) in
    if c <> 0 then c
    else
      let c = compare (count (fun l -> l.positive) a) (count (fun l -> l.positive) b) in
      if c <> 0 then c
      else
        let c = compare (weight a) (weight b) in
        if c <> 0 then c
        else
          let pairwise f = List.fold_left2 (fun acc x y -> if acc <> 0 then acc else f x y) 0 a b in
          let c = pairwise (literal_struct_compare codes) in
          if c <> 0 then c else pairwise (literal_compare codes)

(* UniqWeightCompute (che_clauseweight.c:447): per literal 7 (positive) or 11 (negative) times the
   uniq weights of its two sides; a variable 3, f(t1..tn) 5^n + 2 * sum. *)
let rec uniq_term = function
  | Var _ -> 3.
  | App (_, ts) ->
      List.fold_left (fun w t -> w +. (2. *. uniq_term t)) (5. ** float_of_int (List.length ts)) ts

let uniq_weight lits =
  List.fold_left
    (fun w l -> w +. ((if l.positive then 7. else 11.) *. (uniq_term l.lterm +. uniq_term l.rterm)))
    0. lits

(* E's view of every clause: as written when [text] has its cnf clause ([names]: the source formula
   of each clause), otherwise from the clause itself. *)
let views ?text ?names codes (clauses : clause list) =
  let names = Option.map Array.of_list names in
  List.mapi
    (fun i c ->
      match (text, names) with
      | Some t, Some names -> (
          match if i < Array.length names then names.(i) else None with
          | Some name -> (
              match Hashtbl.find_opt t.clauses name with
              | Some lits when matches c lits -> text_view codes lits
              | _ -> view codes c)
          | _ -> view codes c)
      | _ -> view codes c)
    clauses

(* ClauseSetCanonize: each clause's literals in canonical order, the clauses sorted by
   ClauseStructWeightLexCompare, the last ties by input position (E's clause ident). *)
let sorted_canonical ?text ?names clauses =
  let codes = codes ?text clauses in
  let keyed =
    List.mapi
      (fun i v -> (i, List.stable_sort (literal_compare codes) (List.map (canonize codes) v)))
      (views ?text ?names codes clauses)
  in
  ( codes,
    List.stable_sort
      (fun (i, a) (j, b) ->
        let c = clause_compare codes a b in
        if c <> 0 then c else compare i j)
      keyed )

(** The positions of [clauses] (input order) in E's canonical clause order (ClauseSetCanonize), the
    order in which E looks for equational definitions to unfold. *)
let canonical_order ?text ?names (clauses : clause list) =
  List.map fst (snd (sorted_canonical ?text ?names clauses))

(** The positions of [clauses] (input order) in E's initial evaluation order. With [text] (the
    problem text, {!of_text}) and [names] (each clause's source formula), E's symbol codes and the
    written form of each cnf clause decide the ties, as in E. *)
let order ?text ?names (clauses : clause list) =
  let _, sorted = sorted_canonical ?text ?names clauses in
  List.mapi (fun rank (i, lits) -> (uniq_weight lits, rank, i)) sorted
  |> List.stable_sort compare
  |> List.map (fun (_, _, i) -> i)

(** E's pos_rank of every symbol (TERMS/cte_termfunc.c:2653 TermComputeFunctionRanks via
    ClauseSetComputeFunctionRanks over the canonized axiom set, che_fcode_featurearrays.c:124):
    clauses in E's sorted order, literals in canonical order, each literal's lterm then rterm, terms
    in postorder, each symbol ranked at its first visit; the count starts at 0, so the first symbol
    keeps rank 0 until its next visit ranks it again (the truth constant is visited too). The
    precedence tie-breaker of the E-instance members ({!Eorder.t.e_ranks}). *)
let pos_ranks ?text ?names (clauses : clause list) =
  let codes, sorted = sorted_canonical ?text ?names clauses in
  let key = Hashtbl.create 64 in
  let rec note = function
    | V _ -> ()
    | Fn (f, ts) ->
        Hashtbl.replace key (codes.symbol (symbol_name f)) (Ordering.Function f, List.length ts);
        List.iter note ts
  in
  List.iter
    (List.iter (fun (l : literal) ->
         match l.atom with
         | E (s, t) ->
             note s;
             note t
         | P (p, ts) ->
             Hashtbl.replace key (codes.symbol p) (Ordering.Predicate p, List.length ts);
             List.iter note ts
         | D (d, ts) ->
             Hashtbl.replace key
               (codes.symbol (Printf.sprintf "def%d_%d" (fst d) (snd d)))
               (Ordering.Definition d, List.length ts);
             List.iter note ts))
    clauses;
  Hashtbl.replace key codes.truth (Ordering.Truth, 0);
  let rank = Hashtbl.create 64 and count = ref 0 in
  let visit code =
    match Hashtbl.find_opt key code with
    | None -> ()
    | Some k ->
        if Option.value ~default:0 (Hashtbl.find_opt rank k) = 0 then (
          Hashtbl.replace rank k !count;
          incr count)
  in
  let rec term = function
    | Var _ -> ()
    | App (f, ts) ->
        List.iter term ts;
        visit f
  in
  List.iter
    (fun (_, lits) ->
      List.iter
        (fun l ->
          term l.lterm;
          term l.rterm)
        lits)
    sorted;
  rank
