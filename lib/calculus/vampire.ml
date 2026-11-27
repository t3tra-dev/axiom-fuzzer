open Wire
(** Ported Vampire 5.1.0 slices (Vampire's commit 7b2f410, the source of the comparison binary): the
    options of one schedule entry ("slice"), its symbol precedence and KBO weights, its literal
    selection function and its clause-selection evaluation. A slice member runs the lean
    given-clause loop of the ported E heuristics with these settings instead of E's
    ({!Heuristic.t.vampire}). Every inference is still an ordinary certificate step, so a slice only
    changes which proofs are found, never which are accepted.

    The slice string is Vampire's encoded strategy ("lrs+21_1_sos=on:av=off_1"): saturation
    algorithm, literal selection (negative: reversed polarity), age:weight ratio, options, time in
    deciseconds (Shell/Options.cpp readFromEncodedOptions). {!parse} keeps the options this port
    reproduces and lists the others in [unported]. *)

type saturation =
  | Lrs  (** Limited resource strategy: Otter's loop plus limits from a reachability estimate. *)
  | Otter
  | Discount

(** Shell/Options.hpp SymbolPrecedence (Kernel/Ordering.cpp sortAuxBySymbolPrecedence). *)
type precedence =
  | Frequency
  | Weighted_frequency
  | Reverse_frequency
  | Reverse_weighted_frequency
  | Arity
  | Reverse_arity
  | Occurrence
  | Unary_first
  | Const_max
  | Const_min
  | Unary_frequency
  | Const_frequency

(** KboWeightGenerationScheme (Kernel/KBO.cpp weightsFromOpts). *)
type kbo_weights =
  | Const
  | W_arity
  | Inv_arity
  | Arity_squared
  | Inv_arity_squared
  | W_precedence
  | Inv_precedence
  | W_frequency
  | Inv_frequency

(** LiteralComparisonMode: predicate levels ([Standard]: every non-equality predicate on one level;
    [Predicate] and [Reverse]: levels by predicate precedence, [Reverse] also ranks negative
    literals below positive ones). *)
type lcm = Standard | Predicate | Reverse

(** sine_to_pred_levels: predicate levels from the SInE iteration in which a predicate is first met
    ([No]: conjecture predicates low, [On]: high), with Vampire's decoding of SInE symbol numbers
    (see {!sine_levels}). *)
type s2pl = S2pl_off | S2pl_no | S2pl_on

(** function_definition_elimination (Shell/FunctionDefinition.cpp). *)
type fde = Fde_all | Fde_unused | Fde_none

type t = {
  slice : string;  (** The Vampire slice this ports, as Vampire's schedule writes it. *)
  saturation : saturation;
  selection : int;  (** Vampire's selection number; negative: reversed polarity. *)
  age_ratio : int;
  weight_ratio : int;
  lpo : bool;  (** to=lpo; otherwise KBO. *)
  precedence : precedence;
  kbo_weights : kbo_weights;
  lcm : lcm;
  s2pl : s2pl;
  fde : fde;
  nongoal_weight : int * int;
      (** nwc as Vampire stores it: the weight multiplier of clauses not derived from the negated
          conjecture, and of those that are (Kernel/Clause.cpp computeWeightForClauseSelection; the
          default 10.0 is (10, 1), a value x is (100x, 100)). *)
  avatar : bool;
  sos : bool;
      (** sos=on: the input clauses that are not negated conjectures go to Active without being
          selected (SaturationAlgorithm::addInputSOSClause). *)
  forward_subsumption : bool;
  subsumption_resolution : bool;
  forward_demodulation : bool;
  backward_demodulation : bool;  (** bd (default off). *)
  backward_subsumption : bool;  (** bs (default off). *)
  binary_resolution : bool;  (** br (default on). *)
  unit_resulting : bool;
      (** urr=on: unit resulting resolution (Inferences/URResolution.cpp, not "full": with at most
          one non-ground literal left, the first unifying unit is enough). *)
  literal_rewriting : bool;
      (** flr: forward literal rewriting with equivalences of two-literal clauses
          (Inferences/ForwardLiteralRewriting.cpp, Indexing/LiteralIndex.cpp RewriteRuleIndex). *)
  deciseconds : int;  (** The slice's time limit (the LRS reachability estimate's horizon). *)
  split_at_activation : bool;
      (** sac: AVATAR splits a clause when it is selected (SaturationAlgorithm::activate) instead of
          when it enters Passive (forwardSimplify). *)
  positive_split : bool;
      (** plsq: Passive split by the number of positive literals
          (PositiveLiteralMultiSplitPassiveClauseContainer), with [plsqr] ratios, [plsqc] cutoffs
          and [plsql] arrangement. *)
  plsqr : int list;
  plsqc : float list;
  plsql : bool;
  unported : string list;  (** The slice's options that this port does not reproduce. *)
}

let default =
  {
    slice = "";
    saturation = Lrs;
    selection = 10;
    age_ratio = 1;
    weight_ratio = 1;
    lpo = false;
    precedence = Frequency;
    kbo_weights = Const;
    lcm = Standard;
    s2pl = S2pl_off;
    fde = Fde_all;
    nongoal_weight = (10, 1);
    avatar = true;
    sos = false;
    forward_subsumption = true;
    subsumption_resolution = true;
    forward_demodulation = true;
    backward_demodulation = false;
    backward_subsumption = false;
    literal_rewriting = false;
    unit_resulting = false;
    binary_resolution = true;
    deciseconds = 100;
    split_at_activation = false;
    positive_split = false;
    plsqr = [ 1; 4 ];
    plsqc = [ 0. ];
    plsql = false;
    unported = [];
  }

let precedence_of_string = function
  | "frequency" -> Frequency
  | "weighted_frequency" -> Weighted_frequency
  | "reverse_frequency" -> Reverse_frequency
  | "reverse_weighted_frequency" -> Reverse_weighted_frequency
  | "arity" -> Arity
  | "reverse_arity" -> Reverse_arity
  | "occurrence" -> Occurrence
  | "unary_first" -> Unary_first
  | "const_max" -> Const_max
  | "const_min" -> Const_min
  | "unary_frequency" -> Unary_frequency
  | "const_frequency" -> Const_frequency
  | s -> invalid_arg ("Vampire: unsupported symbol_precedence " ^ s)

let kbo_weights_of_string = function
  | "const" -> Const
  | "arity" -> W_arity
  | "inv_arity" -> Inv_arity
  | "arity_squared" -> Arity_squared
  | "inv_arity_squared" -> Inv_arity_squared
  | "precedence" -> W_precedence
  | "inv_precedence" -> Inv_precedence
  | "frequency" -> W_frequency
  | "inv_frequency" -> Inv_frequency
  | s -> invalid_arg ("Vampire: unsupported kbo_weight_scheme " ^ s)

let supported_selections =
  [ 0; 1; 2; 3; 4; 10; 11; 20; 21; 22; 30; 31; 32; 33; 34; 35; 1002; 1003; 1004; 1010; 1011 ]

(** Lookahead selection (11 complete, 1011 incomplete): the engine counts the inferences each
    candidate literal would have with the Active clauses when the clause is activated ([Engine]);
    without those counts (before activation) it selects as 10 or 1010. *)
let lookahead v = abs v.selection = 11 || abs v.selection = 1011

(* NonGoalWeightOptionValue::setValue: numerator = int (100 x), denominator 100. *)
let nongoal_of_string s =
  match float_of_string_opt s with
  | Some x when x > 0. -> (int_of_float (x *. 100.), 100)
  | _ -> invalid_arg ("Vampire: bad nongoal_weight_coefficient " ^ s)

(* RatioOptionValue::readRatio: "a:w", or "w" for 1:w. *)
let ratio_of_string s =
  match String.split_on_char ':' s with
  | [ w ] -> (1, int_of_string w)
  | [ a; w ] -> (int_of_string a, int_of_string w)
  | _ -> invalid_arg ("Vampire: bad age_weight_ratio " ^ s)

(** Parse an encoded slice (Options::readFromEncodedOptions). The options that only tune parts of
    Vampire this port does not have (random_seed, the SInE and preprocessing options, inference
    rules without a counterpart) are kept in [unported]; the members' documentation lists them. *)
let parse slice =
  let fail () = invalid_arg ("Vampire: bad slice " ^ slice) in
  if String.length slice < 5 then fail ();
  let saturation =
    match String.sub slice 0 3 with
    | "lrs" -> Lrs
    | "ott" -> Otter
    | "dis" -> Discount
    | _ -> fail ()
  in
  let last = match String.rindex_opt slice '_' with Some i -> i | None -> fail () in
  let deciseconds = int_of_string (String.sub slice (last + 1) (String.length slice - last - 1)) in
  let body = String.sub slice 3 (last - 3) in
  let sign, body =
    match body.[0] with
    | '+' -> (1, String.sub body 1 (String.length body - 1))
    | '-' -> (-1, String.sub body 1 (String.length body - 1))
    | _ -> fail ()
  in
  let selection, rest =
    match String.index_opt body '_' with
    | Some i ->
        (int_of_string (String.sub body 0 i), String.sub body (i + 1) (String.length body - i - 1))
    | None -> fail ()
  in
  let awr, options =
    match String.index_opt rest '_' with
    | Some i -> (String.sub rest 0 i, String.sub rest (i + 1) (String.length rest - i - 1))
    | None -> (rest, "")
  in
  let age_ratio, weight_ratio = ratio_of_string awr in
  if not (List.mem selection supported_selections) then
    invalid_arg (Printf.sprintf "Vampire: selection %d is not ported" selection);
  let base =
    {
      default with
      slice;
      saturation;
      selection = sign * selection;
      age_ratio;
      weight_ratio;
      deciseconds;
    }
  in
  List.fold_left
    (fun v option ->
      if option = "" then v
      else
        match String.split_on_char '=' option with
        | [ "to"; "lpo" ] -> { v with lpo = true }
        | [ "to"; ("kbo" | "auto_kbo") ] -> { v with lpo = false }
        | [ "sp"; s ] -> { v with precedence = precedence_of_string s }
        | [ "kws"; s ] -> { v with kbo_weights = kbo_weights_of_string s }
        | [ "lcm"; "standard" ] -> { v with lcm = Standard }
        | [ "lcm"; "predicate" ] -> { v with lcm = Predicate }
        | [ "lcm"; "reverse" ] -> { v with lcm = Reverse }
        | [ "s2pl"; "no" ] -> { v with s2pl = S2pl_no }
        | [ "s2pl"; "on" ] -> { v with s2pl = S2pl_on }
        | [ "s2pl"; "off" ] -> { v with s2pl = S2pl_off }
        | [ "fde"; "all" ] -> { v with fde = Fde_all }
        | [ "fde"; "unused" ] -> { v with fde = Fde_unused }
        | [ "fde"; "none" ] -> { v with fde = Fde_none }
        | [ "nwc"; s ] -> { v with nongoal_weight = nongoal_of_string s }
        | [ "av"; s ] -> { v with avatar = s = "on" }
        | [ "sos"; "on" ] -> { v with sos = true }
        | [ "sos"; "off" ] -> { v with sos = false }
        | [ "fs"; s ] -> { v with forward_subsumption = s = "on" }
        | [ "fsr"; s ] -> { v with subsumption_resolution = s = "on" }
        | [ "fd"; s ] -> { v with forward_demodulation = s <> "off" }
        | [ "bd"; s ] -> { v with backward_demodulation = s <> "off" }
        | [ "bs"; s ] -> { v with backward_subsumption = s <> "off" }
        | [ "flr"; s ] -> { v with literal_rewriting = s = "on" }
        | [ "urr"; "on" ] -> { v with unit_resulting = true }
        | [ "br"; s ] -> { v with binary_resolution = s = "on" }
        | [ "urr"; "off" ] -> { v with unit_resulting = false }
        | [ "sac"; s ] -> { v with split_at_activation = s = "on" }
        | [ "plsq"; s ] -> { v with positive_split = s = "on" }
        | [ "plsqr"; s ] -> { v with plsqr = List.map int_of_string (String.split_on_char ',' s) }
        | [ "plsqc"; s ] -> { v with plsqc = List.map float_of_string (String.split_on_char ',' s) }
        | [ "plsql"; s ] -> { v with plsql = s = "on" }
        | [ "random_seed"; _ ] -> v
        | _ -> { v with unported = v.unported @ [ option ] })
    base
    (String.split_on_char ':' options)

(* ------------------------------------------------------------------------------------------ *)
(* Symbol statistics, precedence and weights (Kernel/Ordering.cpp, Kernel/KBO.cpp,
   Shell/Property.cpp scan). *)

type symbol = {
  head : Ordering.head;
  arity : int;
  id : int;  (** Vampire's symbol number: the order of first occurrence. *)
  mutable usage : int;
      (** usageCnt: occurrences (predicates: times the clause length when weighted). *)
}

(* Function and predicate symbols of the initial clauses in order of first occurrence (clause
   order, literal order, preorder), with their usage counts. Equality is not a symbol here. *)
let statistics ?ids ~weighted (clauses : clause list) =
  let functions = Hashtbl.create 64 and predicates = Hashtbl.create 16 in
  let fn_order = ref [] and pred_order = ref [] in
  let bump table order key arity n =
    match Hashtbl.find_opt table key with
    | Some s -> s.usage <- s.usage + n
    | None ->
        let id =
          match ids with
          | Some ids -> (
              match Hashtbl.find_opt ids key with
              | Some i -> i
              | None -> Hashtbl.length ids + Hashtbl.length table)
          | None -> Hashtbl.length table
        in
        let s = { head = fst key; arity; id; usage = n } in
        Hashtbl.add table key s;
        order := s :: !order
  in
  (* Vampire's TPTP parser adds a function symbol when its application is complete, after its
     arguments (Parse/TPTP.cpp createFunctionApplication): symbol numbers in postorder. *)
  let rec term = function
    | V _ -> ()
    | Fn (f, ts) ->
        List.iter term ts;
        bump functions fn_order (Ordering.Function f, List.length ts) (List.length ts) 1
  in
  List.iter
    (fun (c : clause) ->
      let length = List.length c in
      List.iter
        (fun (l : literal) ->
          match l.atom with
          | E (s, t) ->
              term s;
              term t
          | P (p, ts) ->
              bump predicates pred_order
                (Ordering.Predicate p, List.length ts)
                (List.length ts)
                (if weighted then length else 1);
              List.iter term ts
          | D (d, ts) ->
              bump predicates pred_order
                (Ordering.Definition d, List.length ts)
                (List.length ts)
                (if weighted then length else 1);
              List.iter term ts)
        c)
    clauses;
  let by_id xs = List.stable_sort (fun a b -> compare a.id b.id) (List.rev xs) in
  (by_id !fn_order, by_id !pred_order)

(** Vampire's symbol numbers as its TPTP parser assigns them: function symbols in the order their
    applications complete (postorder, Parse/TPTP.cpp createFunctionApplication), predicates in order
    of first occurrence (equality is predicate 0 and not listed), over the input formulas in file
    order. Predicates are numbered from 0 here; Vampire's number is one more. *)
let parse_order (formulas : source list) =
  let ids = Hashtbl.create 64 in
  let fn = ref 0 and pred = ref 0 in
  let add counter key =
    if not (Hashtbl.mem ids key) then (
      Hashtbl.add ids key !counter;
      incr counter)
  in
  let rec term = function
    | B _ | F _ -> ()
    | App (s, ts) ->
        List.iter term ts;
        add fn (Ordering.Function (Intern.original s), List.length ts)
  in
  let rec formula = function
    | Top | Bot -> ()
    | Pred (p, ts) ->
        List.iter term ts;
        add pred (Ordering.Predicate (Intern.name p), List.length ts)
    | Eq (s, t) ->
        term s;
        term t
    | Neg f | All f | Ex f -> formula f
    | Conj fs | Disj fs -> List.iter formula fs
  in
  List.iter formula formulas;
  ids

(** [parse_order] from the TPTP text itself (Vampire numbers symbols while it parses the file; the
    Source arena keeps formulas in its own canonical order). A light reader of TPTP cnf/fof
    formulas: a term or atom is a name with optional arguments, an atom followed by [=] or [!=] is
    an equation of two terms, otherwise its head is a predicate. Comments, quoted names and include
    directives are not supported (the corpus problems are self-contained); [None] when the text
    cannot be read this way. *)
let parse_order_of_text text =
  let n = String.length text in
  let pos = ref 0 in
  let ids = Hashtbl.create 64 and fn = ref 0 and pred = ref 0 in
  let add counter key =
    if not (Hashtbl.mem ids key) then (
      Hashtbl.add ids key !counter;
      incr counter)
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
  (* A parsed term: its head, its arguments; variables have no symbol. *)
  let rec term () =
    let s = name () in
    let args =
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
        more [])
      else []
    in
    `T (s, args)
  in
  let rec register = function
    | `T (s, args) ->
        List.iter register args;
        let variable = args = [] && s <> "" && s.[0] >= 'A' && s.[0] <= 'Z' in
        if not variable then add fn (Ordering.Function (Intern.original s), List.length args)
  in
  let atom () =
    let t = term () in
    let equation =
      accept "!="
      ||
      (skip ();
       !pos < n
       && text.[!pos] = '='
       && (!pos + 1 >= n || text.[!pos + 1] <> '>')
       &&
       (incr pos;
        true))
    in
    if equation then (
      let u = term () in
      register t;
      register u)
    else
      match t with
      | `T (p, args) ->
          List.iter register args;
          if p <> "$true" && p <> "$false" then
            add pred (Ordering.Predicate (Intern.name p), List.length args)
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
    | _ -> atom ()
  in
  try
    let rec entries () =
      match peek () with
      | None -> ()
      | Some _ ->
          let language = name () in
          if language <> "cnf" && language <> "fof" then raise Unsupported;
          expect '(';
          ignore (name ());
          expect ',';
          ignore (name ());
          expect ',';
          formula ();
          expect ')';
          expect '.';
          entries ()
    in
    entries ();
    Some ids
  with Unsupported | Invalid_argument _ -> None

(* The comparators of sortAuxBySymbolPrecedence, ascending (the first symbol is the smallest).
   [OccurrenceTieBreak] is the symbol number; [FreqComparator] makes rare symbols large. *)
let compare_by scheme a b =
  let id = compare a.id b.id in
  let freq ~rev = if rev then compare a.usage b.usage else compare b.usage a.usage in
  let arity ~rev = if rev then compare b.arity a.arity else compare a.arity b.arity in
  let ( >>> ) c next = if c <> 0 then c else next () in
  let special n ~rev =
    match (a.arity = n, b.arity = n) with
    | true, false -> if rev then -1 else 1
    | false, true -> if rev then 1 else -1
    | _ -> 0
  in
  match scheme with
  | Arity -> arity ~rev:false >>> fun () -> id
  | Reverse_arity -> arity ~rev:true >>> fun () -> id
  | Unary_first ->
      special 1 ~rev:false >>> fun () ->
      arity ~rev:false >>> fun () ->
      freq ~rev:false >>> fun () -> id
  | Const_max ->
      special 0 ~rev:false >>> fun () ->
      arity ~rev:false >>> fun () -> id
  | Const_min ->
      special 0 ~rev:true >>> fun () ->
      arity ~rev:true >>> fun () -> id
  | Frequency | Weighted_frequency -> freq ~rev:false >>> fun () -> id
  | Reverse_frequency | Reverse_weighted_frequency -> freq ~rev:true >>> fun () -> id
  | Unary_frequency ->
      special 1 ~rev:false >>> fun () ->
      freq ~rev:false >>> fun () -> id
  | Const_frequency ->
      special 0 ~rev:true >>> fun () ->
      freq ~rev:false >>> fun () -> id
  | Occurrence -> id

(* Vampire's SInE pass for predicate levels (Shell/Preprocess.cpp, SineSelector with tolerance 1,
   no depth limit, generality threshold 0, Shell/SineUtils.cpp): symbol numbers 3p for a predicate
   p (equality is 0) and 3f + 1 for a function symbol f; every non-goal clause is triggered by its
   least general symbols; a breadth-first pass from the goal clauses gives every predicate it meets
   the current iteration level (starting at 1). Vampire decodes the numbers with [s mod 2] and
   [s / 2] (SineSymbolExtractor::decodeSymId), so the levels land on the predicate numbered
   [s / 2] for every even [s]; a predicate never met gets the final level. This port keeps that
   decoding: it is what the slices' predicate levels are. The result maps Vampire's predicate
   number to its level. *)
let sine_levels ~functions ~predicates ~goal (clauses : clause list) =
  let fid = Hashtbl.create 64 and pid = Hashtbl.create 16 in
  List.iter (fun s -> Hashtbl.replace fid (s.head, s.arity) s.id) functions;
  List.iter (fun s -> Hashtbl.replace pid (s.head, s.arity) (s.id + 1)) predicates;
  let syms (c : clause) =
    let acc = ref [] in
    let rec term = function
      | V _ -> ()
      | Fn (f, ts) ->
          acc := ((3 * Hashtbl.find fid (Ordering.Function f, List.length ts)) + 1) :: !acc;
          List.iter term ts
    in
    List.iter
      (fun (l : literal) ->
        match l.atom with
        | E (s, t) ->
            acc := 0 :: !acc;
            term s;
            term t
        | P (p, ts) ->
            acc := (3 * Hashtbl.find pid (Ordering.Predicate p, List.length ts)) :: !acc;
            List.iter term ts
        | D (d, ts) ->
            acc := (3 * Hashtbl.find pid (Ordering.Definition d, List.length ts)) :: !acc;
            List.iter term ts)
      c;
    List.sort_uniq compare !acc
  in
  let units = Array.of_list (List.map syms clauses) in
  let gen = Hashtbl.create 64 in
  Array.iter
    (List.iter (fun s ->
         Hashtbl.replace gen s (1 + Option.value ~default:0 (Hashtbl.find_opt gen s))))
    units;
  let def = Hashtbl.create 64 in
  Array.iteri
    (fun i ss ->
      if (not (goal i)) && ss <> [] then
        let g s = Hashtbl.find gen s in
        let least = List.fold_left (fun m s -> min m (g s)) max_int ss in
        List.iter
          (fun s ->
            if g s = least then
              Hashtbl.replace def s (i :: Option.value ~default:[] (Hashtbl.find_opt def s)))
          ss)
    units;
  let levels = Hashtbl.create 16 and level = ref 1 in
  let selected = Array.make (Array.length units) false in
  let queue = Queue.create () in
  Array.iteri
    (fun i _ ->
      if goal i then (
        selected.(i) <- true;
        Queue.add (Some i) queue))
    units;
  Queue.add None queue;
  while not (Queue.is_empty queue) do
    match Queue.take queue with
    | None ->
        if !level < 255 then incr level;
        if not (Queue.is_empty queue) then Queue.add None queue
    | Some i ->
        List.iter
          (fun s ->
            if s mod 2 = 0 && not (Hashtbl.mem levels (s / 2)) then
              Hashtbl.add levels (s / 2) !level;
            List.iter
              (fun j ->
                if not selected.(j) then (
                  selected.(j) <- true;
                  Queue.add (Some j) queue))
              (Option.value ~default:[] (Hashtbl.find_opt def s));
            Hashtbl.remove def s)
          units.(i)
  done;
  let bound = !level in
  fun ~reverse p ->
    let l = Option.value ~default:bound (Hashtbl.find_opt levels p) in
    if reverse then bound - l else l

(* KBO::weightsFromOpts: the weight of each function symbol by the scheme ([max] is the largest
   extracted value). Variables weigh 1. *)
let kbo_weight scheme ~max_arity ~max_rank ~max_usage (s : symbol) rank =
  match scheme with
  | Const -> 1
  | W_arity -> s.arity + 1
  | Inv_arity -> max_arity - s.arity + 1
  | Arity_squared -> (s.arity * s.arity) + 1
  | Inv_arity_squared -> (max_arity * max_arity) - (s.arity * s.arity) + 1
  | W_precedence -> rank + 1
  | Inv_precedence -> max_rank - rank + 1
  | W_frequency -> if s.usage > 0 then s.usage else 1
  | Inv_frequency -> if max_usage > 0 then max_usage - s.usage + 1 else 1

(** The ordering table of a slice for {!Ordering.install_table}: [(head, arity) -> (rank, weight)],
    function ranks from the slice's precedence, predicate ranks from the same scheme over the
    predicates (weighted frequencies count each predicate occurrence once per literal of its
    clause), KBO weights from the weight scheme (LPO ignores them). Returns the table and the
    predicate levels of the literal comparison ([lcm]). *)
let table ?goals ?counted ?ids v (clauses : clause list) =
  let weighted =
    match v.precedence with Weighted_frequency | Reverse_weighted_frequency -> true | _ -> false
  in
  let functions, predicates = statistics ?ids ~weighted clauses in
  (* Symbol numbers come from the input as parsed, usage counts from the preprocessed clauses
     (the ordering counts the problem it saturates). *)
  (match counted with
  | None -> ()
  | Some counted ->
      let fs, ps = statistics ~weighted counted in
      let usage = Hashtbl.create 64 in
      List.iter (fun s -> Hashtbl.replace usage (s.head, s.arity) s.usage) (fs @ ps);
      List.iter
        (fun s -> s.usage <- Option.value ~default:0 (Hashtbl.find_opt usage (s.head, s.arity)))
        (functions @ predicates));
  let sorted xs = List.stable_sort (compare_by v.precedence) xs in
  let fs = sorted functions and ps = sorted predicates in
  let tbl = Hashtbl.create 64 in
  let max_of f xs = List.fold_left (fun m s -> max m (f s)) 0 xs in
  let max_arity = max_of (fun s -> s.arity) fs
  and max_usage = max_of (fun s -> s.usage) fs
  and max_rank = max 0 (List.length fs - 1) in
  List.iteri
    (fun rank s ->
      Hashtbl.replace tbl (s.head, s.arity)
        (rank, kbo_weight v.kbo_weights ~max_arity ~max_rank ~max_usage s rank))
    fs;
  List.iteri (fun rank s -> Hashtbl.replace tbl (s.head, s.arity) (rank, 1)) ps;
  let levels = Hashtbl.create 16 and ids = Hashtbl.create 64 in
  List.iteri
    (fun rank s ->
      Hashtbl.replace levels (s.head, s.arity) (match v.lcm with Standard -> 1 | _ -> 1 + rank))
    ps;
  (match goals with
  | Some goal when v.s2pl <> S2pl_off ->
      let sine = sine_levels ~functions ~predicates ~goal clauses in
      List.iter
        (fun s ->
          let level = sine ~reverse:(v.s2pl = S2pl_on) (s.id + 1) in
          Hashtbl.replace levels (s.head, s.arity) level)
        predicates
  | _ -> ());
  List.iter (fun s -> Hashtbl.replace ids (s.head, s.arity) s.id) functions;
  List.iter (fun s -> Hashtbl.replace ids (s.head, s.arity) s.id) predicates;
  (tbl, levels, ids)

(** Diagnostics hook (the CLI's AXIOM_VAMPIRE_ORDERING): the installed precedences, weights and
    predicate levels, in --show_ordering's order, smallest first. *)
let report : (string -> unit) ref = ref (fun _ -> ())

let name_of = function
  | Ordering.Function (Original f) -> f
  | Ordering.Function (Skolem (a, i)) -> Printf.sprintf "sk%d_%d" a i
  | Ordering.Predicate p -> p
  | Ordering.Definition (a, i) -> Printf.sprintf "def%d_%d" a i
  | Ordering.Truth -> "$true"

(** Install the slice's ordering on [order] ({!Ordering.install_table}): the table, KBO or LPO, and
    Vampire's literal comparison with the predicate levels. *)
let install ?goals ?counted ?ids v order (clauses : clause list) =
  let tbl, levels, sym_ids = table ?goals ?counted ?ids v clauses in
  let entries = Hashtbl.fold (fun (h, n) (rank, w) acc -> (h, n, rank, w) :: acc) tbl [] in
  let functions =
    List.filter
      (fun (h, _, _, _) -> match h with Ordering.Function _ -> true | _ -> false)
      entries
    |> List.sort (fun (_, _, a, _) (_, _, b, _) -> compare a b)
  and predicates =
    List.filter
      (fun (h, _, _, _) -> match h with Ordering.Function _ -> false | _ -> true)
      entries
    |> List.sort (fun (_, _, a, _) (_, _, b, _) -> compare a b)
  in
  let usage = Hashtbl.create 64 in
  let fs, ps = statistics ?ids ~weighted:false clauses in
  List.iter (fun s -> Hashtbl.replace usage (s.head, s.arity) (s.usage, s.id)) (fs @ ps);
  let u h n = Option.value ~default:(0, 0) (Hashtbl.find_opt usage (h, n)) in
  List.iter
    (fun (h, n, _, w) ->
      !report
        (Printf.sprintf "vampire-order: function %s %d weight %d usage %d id %d" (name_of h) n w
           (fst (u h n))
           (snd (u h n))))
    functions;
  !report (Printf.sprintf "vampire-order: clauses %d" (List.length clauses));
  List.iter
    (fun (h, n, _, _) ->
      !report
        (Printf.sprintf "vampire-order: predicate %s %d level %d id %d" (name_of h) n
           (Option.value ~default:0 (Hashtbl.find_opt levels (h, n)))
           (snd (u h n))))
    predicates;
  Ordering.install_table
    ~kind:(if v.lpo then Ordering.Lpo else Ordering.Kbo)
    ~vampire:{ Ordering.levels; reverse = v.lcm = Reverse; ids = sym_ids }
    order tbl

(* ------------------------------------------------------------------------------------------ *)
(* Preprocessing of the input clauses (Shell/Preprocess.cpp): function definition elimination,
   then equality resolution with deletion. *)

(** FunctionDefinition::isFunctionDefinition for a non-constant symbol: a positive unit equation
    between two non-variable terms, one of them f(X1,...,Xn) with distinct variables, f not in the
    other side, every variable of which is an Xi; the left side first. Definitions of constants
    (Vampire's two-constant definitions) are not ported. *)
let definition (c : clause) =
  match c with [ { positive = true; atom = E (Fn _, Fn _) } ] -> Unfold.definition c | _ -> None

let rec functions_of acc = function
  | V _ -> acc
  | Fn (f, ts) -> List.fold_left functions_of ((f, List.length ts) :: acc) ts

let clause_functions (c : clause) =
  List.fold_left
    (fun acc (l : literal) -> List.fold_left functions_of acc (Clause.atom_terms l.atom))
    [] c

(** EqResWithDeletion::apply on one clause: while some negative equation x != t (or t != x) has a
    variable x not in t, the first such literal is removed and x := t applied. *)
let rec eq_res_with_deletion (c : clause) =
  let rec occurs x = function V y -> x = y | Fn (_, ts) -> List.exists (occurs x) ts in
  let candidate (l : literal) =
    match (l.positive, l.atom) with
    | false, E (V x, t) when not (occurs x t) -> Some (x, t)
    | false, E (t, V x) when not (occurs x t) -> Some (x, t)
    | _ -> None
  in
  let rec find i = function
    | [] -> None
    | l :: rest -> ( match candidate l with Some b -> Some (i, b) | None -> find (i + 1) rest)
  in
  match find 0 c with
  | None -> c
  | Some (i, (x, t)) ->
      let rec sub = function
        | V y when y = x -> t
        | V _ as v -> v
        | Fn (f, ts) -> Fn (f, List.map sub ts)
      in
      eq_res_with_deletion (List.map (Clause.map_literal sub) (List.filteri (fun j _ -> j <> i) c))

type preprocessed = {
  plan : Unfold.plan option;
      (** The removed definitions and the rewritten clauses, for the engine's unfolding path
          ([None]: nothing removed). *)
  order : int list;
      (** Input positions in Vampire's order: definitions that stay first (FunctionDefinition puts
          them back at the front of the unit list), then the other clauses. *)
  counted : clause list;
      (** The clauses after preprocessing (definitions removed and unfolded, equality resolution
          with deletion applied), whose symbol counts give the precedence. *)
}

(** The slice's function definition elimination over the input [clauses] (input order): [Fde_unused]
    removes, iteratively, definitions whose symbol occurs nowhere else
    (FunctionDefinition::removeUnusedDefinitions); [Fde_all] unfolds every definition whose
    unfolding does not cycle, in an order where each one uses only earlier ones, and removes them
    (removeAllDefinitions; a definition that would close a cycle stays). The first definition of
    each symbol is the candidate. *)
let preprocess v (clauses : clause list) =
  let xs = Array.of_list clauses in
  let n = Array.length xs in
  let defs = Hashtbl.create 16 and first = ref [] in
  Array.iteri
    (fun i c ->
      match definition c with
      | Some d when not (Hashtbl.mem defs (d.symbol, d.arity)) ->
          Hashtbl.replace defs (d.symbol, d.arity) (i, d);
          first := i :: !first
      | _ -> ())
    xs;
  let candidates = List.rev !first in
  let removed = Array.make n false in
  let order_removed = ref [] in
  (match v.fde with
  | Fde_none -> ()
  | Fde_unused ->
      let occ = Hashtbl.create 64 in
      Array.iter
        (fun c ->
          List.iter
            (fun k -> Hashtbl.replace occ k (1 + Option.value ~default:0 (Hashtbl.find_opt occ k)))
            (clause_functions c))
        xs;
      let count k = Option.value ~default:0 (Hashtbl.find_opt occ k) in
      let todo = Stack.create () in
      List.iter
        (fun i ->
          match definition xs.(i) with
          | Some d when count (d.symbol, d.arity) = 1 -> Stack.push i todo
          | _ -> ())
        candidates;
      while not (Stack.is_empty todo) do
        let i = Stack.pop todo in
        if not removed.(i) then (
          removed.(i) <- true;
          order_removed := i :: !order_removed;
          List.iter
            (fun k ->
              Hashtbl.replace occ k (count k - 1);
              if count k = 1 then
                match Hashtbl.find_opt defs k with
                | Some (j, _) when not removed.(j) -> Stack.push j todo
                | _ -> ())
            (clause_functions xs.(i)))
      done
  | Fde_all ->
      (* checkDefinitions: a depth-first walk through the right sides; a definition reached again
         while it is being entered is blocked; the others become safe in post-order. *)
      let state = Hashtbl.create 16 in
      let safe = ref [] in
      let rec visit k =
        match Hashtbl.find_opt defs k with
        | None -> ()
        | Some (i, d) -> (
            match Hashtbl.find_opt state k with
            | Some `Safe | Some `Blocked -> ()
            | Some `Loop -> Hashtbl.replace state k `Blocked
            | None ->
                Hashtbl.replace state k `Loop;
                let _, rhs = Unfold.sides d xs.(i) in
                List.iter visit (List.rev (functions_of [] rhs));
                if Hashtbl.find_opt state k = Some `Loop then (
                  Hashtbl.replace state k `Safe;
                  safe := i :: !safe))
      in
      List.iter
        (fun i -> match definition xs.(i) with Some d -> visit (d.symbol, d.arity) | None -> ())
        candidates;
      List.iter
        (fun i ->
          removed.(i) <- true;
          order_removed := i :: !order_removed)
        (List.rev !safe));
  let removed_list = List.rev !order_removed in
  let current = Array.map (fun c -> c) xs in
  let steps = ref 0 and rewritten = Array.make n false in
  (* Each removed definition rewrites every clause not removed before it (Unfold's plan order). *)
  let gone = Array.make n false in
  if v.fde = Fde_all then
    List.iter
      (fun p ->
        match definition current.(p) with
        | Some d ->
            gone.(p) <- true;
            let lhs, rhs = Unfold.sides d current.(p) in
            Array.iteri
              (fun q c ->
                if not gone.(q) then
                  let count = ref 0 in
                  let c' = Unfold.unfold_clause d (lhs, rhs) count c in
                  if !count > 0 then (
                    steps := !steps + !count;
                    current.(q) <- Unfold.dedup c';
                    rewritten.(q) <- true))
              current
        | None -> ())
      removed_list;
  let kept_definitions =
    List.filter (fun i -> (not removed.(i)) && definition xs.(i) <> None) (List.init n Fun.id)
  in
  let others =
    List.filter (fun i -> not (removed.(i) || List.mem i kept_definitions)) (List.init n Fun.id)
  in
  let order = kept_definitions @ others in
  let plan =
    if removed_list = [] then None
    else
      Some
        {
          Unfold.removed =
            List.map
              (fun p ->
                match definition current.(p) with
                | Some d -> (p, d)
                | None -> (p, Option.get (definition xs.(p))))
              removed_list;
          clauses = current;
          conjecture = Array.make n false;
          steps = !steps;
          rewritten = Array.fold_left (fun k b -> if b then k + 1 else k) 0 rewritten;
        }
  in
  { plan; order; counted = List.map (fun i -> eq_res_with_deletion current.(i)) order }

(* ------------------------------------------------------------------------------------------ *)
(* Clause selection (Saturation/AWPassiveClauseContainers.cpp). *)

let rec term_weight = function
  | V _ -> 1
  | Fn (_, ts) -> List.fold_left (fun n t -> n + term_weight t) 1 ts

(** Literal::weight: the predicate (or equality) symbol, every function symbol and every variable
    occurrence count 1. *)
let literal_weight (l : literal) =
  match l.atom with
  | E (s, t) -> 1 + term_weight s + term_weight t
  | P (_, ts) | D (_, ts) -> List.fold_left (fun n t -> n + term_weight t) 1 ts

let clause_weight (c : clause) = List.fold_left (fun n l -> n + literal_weight l) 0 c

(** weightForClauseSelection: the weight times the nongoal multiplier for a clause not derived from
    the negated conjecture, times the goal multiplier otherwise. *)
let selection_weight v ~goal c =
  let nongoal, goal_multiplier = v.nongoal_weight in
  clause_weight c * if goal then goal_multiplier else nongoal

(** The evaluations of a clause for the age and weight queues, as Passive's queue mix orders them
    ((priority, weight, id) ascending): AgeQueue::lessThan (age, weight, input type, number) and
    WeightQueue::lessThan (weight, age, input type, number). A clause derived from the negated
    conjecture has the larger input type, which Vampire selects first on a tie. *)
let evaluations v ~age ~goal c =
  let w = selection_weight v ~goal c and tie = if goal then 0 else 1 in
  [| (age, float_of_int ((2 * w) + tie)); (w, float_of_int ((2 * age) + tie)) |]

(* ------------------------------------------------------------------------------------------ *)
(* A persistent most general unifier on Wire terms (for unit resulting resolution). *)

let rec apply sigma = function
  | V v as t -> ( match List.assoc_opt v sigma with None -> t | Some t -> apply sigma t)
  | Fn (f, ts) -> Fn (f, List.map (apply sigma) ts)

let rec occurs v = function V w -> v = w | Fn (_, ts) -> List.exists (occurs v) ts

let unify equations =
  let rec solve sigma = function
    | [] -> Some (List.map (fun (v, t) -> (v, apply sigma t)) sigma)
    | (s, t) :: rest -> (
        let s = apply sigma s and t = apply sigma t in
        if s = t then solve sigma rest
        else
          match (s, t) with
          | V v, t | t, V v -> if occurs v t then None else solve ((v, t) :: sigma) rest
          | Fn (f, ss), Fn (g, ts) when f = g && List.length ss = List.length ts ->
              solve sigma (List.combine ss ts @ rest)
          | _ -> None)
  in
  solve [] equations

(** The unifiers that make [l] and [m] complementary (both orientations of an equation). *)
let complementary_unifiers (l : literal) (m : literal) =
  if l.positive = m.positive then []
  else
    match (l.atom, m.atom) with
    | P (p, xs), P (q, ys) when p = q && List.length xs = List.length ys ->
        Option.to_list (unify (List.combine xs ys))
    | D (p, xs), D (q, ys) when p = q && List.length xs = List.length ys ->
        Option.to_list (unify (List.combine xs ys))
    | E (s, t), E (u, w) -> List.filter_map unify [ [ (s, u); (t, w) ]; [ (s, w); (t, u) ] ]
    | _ -> []

(* ------------------------------------------------------------------------------------------ *)
(* The limited resource strategy (Saturation/LRS.cpp, AWPassiveClauseContainers.cpp), on the
   engine's deterministic work clock instead of the wall clock. *)

type limits = { max_age : int; max_age_weight : int; max_weight : int }
(** The selection limits: the age and weight at which the age queue stands, and the weight at which
    the weight queue stands, after the simulated selections ([max_int]: no limit). *)

let no_limits = { max_age = max_int; max_age_weight = max_int; max_weight = max_int }

(** From [Passive.simulate_balance]: the queues' evaluations ([evaluations]: the age queue's weight
    component is [2 * weight + tie]). lrs_weight_limit_only (lwlo) is not ported. *)
let limits_of (age, weight) =
  let max_age, max_age_weight =
    match age with Some (a, f) -> (a, int_of_float f / 2) | None -> (max_int, max_int)
  in
  { max_age; max_age_weight; max_weight = (match weight with Some (w, _) -> w | None -> max_int) }

(** AWPassiveClauseContainer::exceedsAllLimits for a clause of [age] and selection weight [w]. *)
let exceeds_all_limits l ~age ~weight =
  if age < l.max_age then false
  else if weight <= l.max_weight then false
  else if age > l.max_age then true
  else weight > l.max_age_weight

(** LRS::estimatedReachableCount on the work clock: nothing before lrs_first_time_check (5 % of the
    budget); then the activations so far times the remaining budget over the work spent since the
    first activation (lrs_estimate_correction_coef 1). [None]: no estimate yet. *)
let reachable ~activations ~elapsed ~since_first ~budget =
  if budget <= 0 || elapsed * 100 < 5 * budget then None
  else
    let left = budget - elapsed in
    if left <= 0 || since_first <= 0 then None
    else
      Some
        (int_of_float (float_of_int activations *. float_of_int left /. float_of_int since_first))

(* ------------------------------------------------------------------------------------------ *)
(* Literal selection (Kernel/LiteralSelector.cpp and the selectors it builds). The result is the
   list of selected literal indices, never empty for a nonempty clause. *)

let reversed v = v.selection < 0

(* LiteralSelector::isNegativeForSelection: equalities keep their sign. *)
let negative_for_selection v (l : literal) =
  match l.atom with E _ -> not l.positive | _ -> if reversed v then l.positive else not l.positive

let rec num_var_occs = function
  | V _ -> 1
  | Fn (_, ts) -> List.fold_left (fun n t -> n + num_var_occs t) 0 ts

let atom_args (l : literal) = match l.atom with E (s, t) -> [ s; t ] | P (_, ts) | D (_, ts) -> ts
let literal_var_occs l = List.fold_left (fun n t -> n + num_var_occs t) 0 (atom_args l)

let distinct_vars l =
  List.length (List.sort_uniq compare (Wire.variables [ { l with positive = true } ]))

let top_level_vars l =
  List.length (List.filter (function V _ -> true | Fn _ -> false) (atom_args l))

let positive_equality (l : literal) = match l.atom with E _ -> l.positive | _ -> false
let negative_equality (l : literal) = match l.atom with E _ -> not l.positive | _ -> false
let ground (l : literal) = Wire.variables [ l ] = []

(* LexComparator on [ids] (the symbol numbers of the installed statistics): the header (predicate
   number, then polarity), then the preorder subterms' functors and variables. *)
let lex_compare ~id (a : literal) (b : literal) =
  let header (l : literal) =
    let p =
      match l.atom with
      | E _ -> -1
      | P (p, ts) -> id (Ordering.Predicate p, List.length ts)
      | D (d, ts) -> id (Ordering.Definition d, List.length ts)
    in
    (p, if l.positive then 1 else 0)
  in
  let c = compare (header a) (header b) in
  if c <> 0 then c
  else
    let rec preorder acc = function
      | V v -> `V v :: acc
      | Fn (f, ts) ->
          List.fold_left preorder (`F (id (Ordering.Function f, List.length ts)) :: acc) ts
    in
    let flat l = List.rev (List.fold_left preorder [] (atom_args l)) in
    let rec go xs ys =
      match (xs, ys) with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | x :: xs, y :: ys -> (
          match (x, y) with
          | `F f, `F g -> if f <> g then compare f g else go xs ys
          | `F _, `V _ -> 1
          | `V _, `F _ -> -1
          | `V u, `V w -> if u <> w then compare u w else go xs ys)
    in
    go (flat a) (flat b)

(* The quality comparators of LiteralSelector::getSelector (greater = better). *)
let quality v ~id number a b =
  let bool_cmp x y = compare (if x then 1 else 0) (if y then 1 else 0) in
  let ( >>> ) c next = if c <> 0 then c else next () in
  let no_positive_equality () = bool_cmp (not (positive_equality a)) (not (positive_equality b)) in
  let least_tlv () = compare (top_level_vars b) (top_level_vars a) in
  let least_distinct () = compare (distinct_vars b) (distinct_vars a) in
  let least_vars () = compare (literal_var_occs b) (literal_var_occs a) in
  let maximal_size () = compare (literal_weight a) (literal_weight b) in
  let lex () = lex_compare ~id a b in
  match number mod 1000 with
  | 2 -> maximal_size () >>> lex
  | 3 ->
      no_positive_equality () >>> fun () ->
      least_tlv () >>> fun () -> least_distinct () >>> lex
  | 4 ->
      no_positive_equality () >>> fun () ->
      least_tlv () >>> fun () ->
      least_vars () >>> fun () -> maximal_size () >>> lex
  | 10 ->
      bool_cmp (negative_equality a) (negative_equality b) >>> fun () ->
      maximal_size () >>> fun () ->
      bool_cmp (negative_for_selection v a) (negative_for_selection v b) >>> lex
  | _ -> invalid_arg "Vampire.quality"

(** The selected literals of [clause] under the slice's selection; [greater i j]: literal [i]
    exceeds literal [j] in the installed (Vampire) literal order. *)
let select v ~id ~greater (clause : clause) =
  let xs = Array.of_list clause in
  let n = Array.length xs in
  let all = List.init n Fun.id in
  (* Ordering::removeNonMaximal: the literals that no other one of [among] exceeds. *)
  let maximal_among among =
    List.filter (fun i -> not (List.exists (fun j -> j <> i && greater j i) among)) among
  in
  let maximals () = maximal_among all in
  if n <= 1 then all
  else
    let number = match abs v.selection with 11 -> 10 | 1011 -> 1010 | k -> k in
    match number with
    | 0 -> all
    | 1 -> (
        (* MaximalLiteralSelector: with a negative literal, the first negative literal that no
           other negative one exceeds; otherwise every maximal literal. *)
        match List.filter (fun i -> negative_for_selection v xs.(i)) all with
        | [] -> maximals ()
        | negatives -> [ List.hd (maximal_among negatives) ])
    | 2 | 3 | 4 | 10 -> (
        (* CompleteBestLiteralSelector: the literals sorted best first; the best negative literal
           unless every maximal literal is better than it; one maximal literal is selected
           alone. *)
        let sorted = List.stable_sort (fun i j -> quality v ~id number xs.(j) xs.(i)) all in
        let ms = maximals () in
        let single =
          match sorted with
          | best :: _ when negative_for_selection v xs.(best) -> Some best
          | _ ->
              let rec walk remaining = function
                | [] -> None
                | i :: rest -> (
                    let remaining = List.filter (( <> ) i) remaining in
                    if remaining = [] then None
                    else
                      match rest with
                      | j :: _ when negative_for_selection v xs.(j) -> Some j
                      | _ -> walk remaining rest)
              in
              walk ms sorted
        in
        match single with Some i -> [ i ] | None -> ( match ms with [ m ] -> [ m ] | _ -> ms))
    | 1002 | 1003 | 1004 | 1010 ->
        (* BestLiteralSelector: the single best literal (the first one on a tie). *)
        let best =
          List.fold_left
            (fun best i -> if quality v ~id number xs.(best) xs.(i) < 0 then i else best)
            0 (List.tl all)
        in
        [ best ]
    | 20 | 21 | 22 -> (
        (* SpassLiteralSelector: OFF / IFSEVERALMAXIMAL / ALWAYS select a heaviest negative literal
           (the last one on a tie); otherwise every maximal literal. *)
        let ms = maximals () in
        let try_negative = number = 22 || (number = 21 && List.length ms > 1) in
        let single =
          if not try_negative then None
          else
            List.fold_left
              (fun best i ->
                if not (negative_for_selection v xs.(i)) then best
                else
                  match best with
                  | Some b when literal_weight xs.(b) >= literal_weight xs.(i) -> best
                  | _ -> Some i)
              None (List.rev all)
        in
        match single with Some i -> [ i ] | None -> ms)
    | 30 | 31 | 32 | 33 | 34 | 35 ->
        (* ELiteralSelector (Kernel/ELiteralSelector.cpp); iteration from the last literal. *)
        let negatives = List.filter (fun i -> negative_for_selection v xs.(i)) (List.rev all) in
        let diff (l : literal) =
          match l.atom with
          | E (s, t) -> abs (term_weight s - term_weight t)
          | _ -> literal_weight l - 1
        in
        let diff_weight l = (100 * diff l) + literal_weight l in
        let best_by key candidates =
          List.fold_left
            (fun best i ->
              match best with
              | Some (bv, _) when key xs.(i) <= bv -> best
              | _ -> Some (key xs.(i), i))
            None candidates
          |> Option.map snd
        in
        let selected =
          match number with
          | 30 -> negatives
          | 31 ->
              Option.to_list
                (List.find_opt
                   (fun i -> match xs.(i).atom with E (V _, V _) -> true | _ -> false)
                   negatives)
          | 32 ->
              Option.to_list
                (List.fold_left
                   (fun best i ->
                     match best with
                     | Some b when literal_weight xs.(b) <= literal_weight xs.(i) -> best
                     | _ -> Some i)
                   None negatives)
          | 33 -> Option.to_list (best_by diff_weight negatives)
          | 34 ->
              Option.to_list (best_by diff_weight (List.filter (fun i -> ground xs.(i)) negatives))
          | _ ->
              (* SelectOptimalLit: ground literals first, then the greatest diff weight. *)
              let grounds = List.filter (fun i -> ground xs.(i)) negatives in
              Option.to_list (best_by diff_weight (if grounds <> [] then grounds else negatives))
        in
        if selected = [] then maximals () else List.sort compare selected
    | _ -> invalid_arg (Printf.sprintf "Vampire: selection %d is not ported" v.selection)

(** LookaheadLiteralSelector::pickTheBest's tie break among the literals with the fewest inferences
    (greater is better): no positive equality, fewest top-level variables, fewest distinct
    variables, then the lexical order. *)
let lookahead_tie ~id a b =
  let bool_cmp x y = compare (if x then 1 else 0) (if y then 1 else 0) in
  let ( >>> ) c next = if c <> 0 then c else next () in
  bool_cmp (not (positive_equality a)) (not (positive_equality b)) >>> fun () ->
  compare (top_level_vars b) (top_level_vars a) >>> fun () ->
  compare (distinct_vars b) (distinct_vars a) >>> fun () -> lex_compare ~id a b

(** A selection function that may select a literal another literal exceeds (1002-1010): Vampire does
    no maximality after-check for it (isBGComplete false). *)
let incomplete v = abs v.selection >= 1000

(** Whether the slice is refutationally complete as a calculus (the LRS limits aside): no set of
    support (sos=on never lets two input axioms meet) and a complete selection. *)
let complete v = (not v.sos) && not (incomplete v)
