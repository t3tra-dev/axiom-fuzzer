open Wire

exception Error of string

let quote s =
  "'"
  ^ String.concat ""
      (List.init (String.length s) (fun i ->
           match s.[i] with '\'' -> "\\'" | '\\' -> "\\\\" | c -> String.make 1 c))
  ^ "'"

let application name ts = if ts = [] then name else name ^ "(" ^ String.concat "," ts ^ ")"

let source f =
  let rec term env = function
    | B i -> List.nth env i
    | F i -> "F" ^ string_of_int i
    | App (s, ts) -> application (quote s) (List.map (term env) ts)
  in
  let rec formula env = function
    | Top -> "$true"
    | Bot -> "$false"
    | Pred (p, ts) -> application (quote p) (List.map (term env) ts)
    | Eq (x, y) -> "(" ^ term env x ^ " = " ^ term env y ^ ")"
    | Neg f -> "~(" ^ formula env f ^ ")"
    | Conj [] -> "$true"
    | Disj [] -> "$false"
    | Conj fs -> "(" ^ String.concat " & " (List.map (formula env) fs) ^ ")"
    | Disj fs -> "(" ^ String.concat " | " (List.map (formula env) fs) ^ ")"
    | All f -> quant "!" env f
    | Ex f -> quant "?" env f
  and quant q env f =
    let x = "X" ^ string_of_int (List.length env) in
    q ^ "[" ^ x ^ "]: (" ^ formula (x :: env) f ^ ")"
  in
  formula [] f

(* Search Skolem symbols and source function names use disjoint exported names. *)
let symbol = function
  | Original s -> quote ("src_" ^ s)
  | Skolem (a, i) -> Printf.sprintf "sk_%d_%d" a i

let rec term = function
  | V (s, i) -> Printf.sprintf "V%d_%d" s i
  | Fn (f, ts) -> application (symbol f) (List.map term ts)

let definition_symbol (a, i) = Printf.sprintf "def_%d_%d" a i

let atom = function
  | P (p, ts) -> application (quote ("srcp_" ^ p)) (List.map term ts)
  | D (id, ts) -> application (definition_symbol id) (List.map term ts)
  | E (x, y) -> "(" ^ term x ^ " = " ^ term y ^ ")"

let clause c =
  match c with
  | [] -> "$false"
  | _ ->
      String.concat " | "
        (List.map (fun l -> if l.positive then atom l.atom else "~(" ^ atom l.atom ^ ")") c)

let rec rename_source_terms = function
  | App (s, ts) -> App ("src_" ^ s, List.map rename_source_terms ts)
  | t -> t

let rec search_source = function
  | Pred (p, ts) -> Pred ("srcp_" ^ p, List.map rename_source_terms ts)
  | Eq (x, y) -> Eq (rename_source_terms x, rename_source_terms y)
  | Neg f -> Neg (search_source f)
  | Conj fs -> Conj (List.map search_source fs)
  | Disj fs -> Disj (List.map search_source fs)
  | All f -> All (search_source f)
  | Ex f -> Ex (search_source f)
  | f -> f

let problem axioms =
  String.concat "\n"
    (List.map
       (fun (a : axiom) -> Printf.sprintf "fof(ax_%d,axiom,(%s))." a.axiom_id (source a.formula))
       axioms)

let cnf_problem ?(mode = Hybrid) axioms =
  List.concat_map
    (fun (a : axiom) ->
      Clausify.run ~mode a
      |> List.mapi (fun i c -> Printf.sprintf "cnf(ax_%d_%d,axiom,(%s))." a.axiom_id i (clause c)))
    axioms
  |> String.concat "\n"

let tstp (cert : certificate) =
  if Option.is_some cert.natural then invalid_arg "TSTP: natural-deduction proofs use --rocq output";
  let support =
    match cert.avatar with None -> fun _ -> [] | Some a -> Avatar_proof.validate cert.steps a
  in
  let label id = "avatar_b_" ^ string_of_int id in
  let boolean_literal l =
    let name = label (Avatar_proof.component_of_literal l) in
    if l > 0 then name else "~" ^ name
  in
  let disjoin = function [] -> "$false" | xs -> String.concat " | " xs in
  let component_definitions =
    match cert.avatar with
    | None -> []
    | Some a ->
        List.mapi
          (fun id c ->
            let vars = Wire.variables c |> List.map (fun (s, i) -> Printf.sprintf "V%d_%d" s i) in
            let body =
              if vars = [] then clause c
              else "![" ^ String.concat "," vars ^ "]: (" ^ clause c ^ ")"
            in
            Printf.sprintf
              "fof(component_%d,definition,(%s <=> \
               (%s)),introduced(definition,[new_symbols(definition,[%s])]))."
              id (label id) body (label id))
          a.components
  in
  let sources =
    List.map
      (fun (a : axiom) ->
        Printf.sprintf "fof(ax_%d,axiom,(%s))." a.axiom_id (source (search_source a.formula)))
      cert.axioms
  in
  let introductions = Hashtbl.create 32 in
  let rec skolems acc = function
    | V _ -> acc
    | Fn (s, ts) -> List.fold_left skolems (match s with Skolem _ -> s :: acc | _ -> acc) ts
  in
  let input_groups =
    List.map
      (fun (a : axiom) ->
        let cs = Clausify.run ~mode:cert.cnf_mode a in
        let symbols =
          List.fold_left
            (fun acc c ->
              List.fold_left
                (fun acc l ->
                  match l.atom with
                  | P (_, ts) | D (_, ts) -> List.fold_left skolems acc ts
                  | E (x, y) -> skolems (skolems acc x) y)
                acc c)
            [] cs
          |> List.sort_uniq compare
        in
        let definitions =
          List.concat cs
          |> List.filter_map (fun l -> match l.atom with D (id, _) -> Some id | _ -> None)
          |> List.sort_uniq compare
        in
        let form =
          match cs with
          | [] -> "$true"
          | _ ->
              String.concat " & "
                (List.map
                   (fun c ->
                     let vars =
                       Wire.variables c |> List.map (fun (s, i) -> Printf.sprintf "V%d_%d" s i)
                     in
                     if vars = [] then "(" ^ clause c ^ ")"
                     else "(![" ^ String.concat "," vars ^ "]: (" ^ clause c ^ "))")
                   cs)
        in
        List.iteri (fun i _ -> Hashtbl.add introductions (a.axiom_id, i) ()) cs;
        let auxiliary =
          if definitions = [] then ""
          else
            ",new_symbols(definition,["
            ^ String.concat "," (List.map definition_symbol definitions)
            ^ "])"
        in
        Printf.sprintf
          "fof(cnf_%d,plain,(%s),inference(clausification,[status(esa),new_symbols(skolem,[%s])%s],[ax_%d]))."
          a.axiom_id form
          (String.concat "," (List.map symbol symbols))
          auxiliary a.axiom_id)
      cert.axioms
  in
  let steps =
    List.map
      (fun (s : step) ->
        let rule, parents =
          match s.rule with
          | Input (a, i) ->
              if not (Hashtbl.mem introductions (a, i)) then invalid_arg "TSTP: missing input";
              ("conjunct", [ "cnf_" ^ string_of_int a ])
          | Component id -> ("avatar_component", [ "component_" ^ string_of_int id ])
          | Resolve (p, _, q, _, _) ->
              ("resolution", List.map (fun i -> "c" ^ string_of_int i) [ p; q ])
          | Factor (p, _, _, _) -> ("factoring", [ "c" ^ string_of_int p ])
          | Equality_resolve (p, _, _) -> ("equality_resolution", [ "c" ^ string_of_int p ])
          | Equality_factor (p, _, _, _, _, _) -> ("equality_factoring", [ "c" ^ string_of_int p ])
          | Paramodulate (p, _, _, q, _, _, _) ->
              ("paramodulation", List.map (fun i -> "c" ^ string_of_int i) [ p; q ])
        in
        let guards = List.map (fun id -> "~" ^ label id) (support s.id) in
        let formula = disjoin (guards @ if s.clause = [] then [] else [ clause s.clause ]) in
        Printf.sprintf "cnf(c%d,plain,(%s),inference(%s,[status(thm)],[%s]))." s.id formula rule
          (String.concat "," parents))
      cert.steps
  in
  let boolean_steps =
    match cert.avatar with
    | None -> []
    | Some a ->
        let splits = Array.of_list a.splits in
        List.map
          (fun s ->
            let rule, parents =
              match s.boolean_rule with
              | Split i ->
                  let parent, ids = splits.(i) in
                  ( "avatar_split",
                    ("c" ^ string_of_int parent)
                    :: List.map (fun id -> "component_" ^ string_of_int id) ids )
              | Conflict id -> ("avatar_conflict", [ "c" ^ string_of_int id ])
              | Boolean_resolve (p, _, q) ->
                  ("resolution", [ "b" ^ string_of_int p; "b" ^ string_of_int q ])
            in
            Printf.sprintf "cnf(b%d,plain,(%s),inference(%s,[status(thm)],[%s]))." s.boolean_id
              (disjoin (List.map boolean_literal s.boolean_clause))
              rule (String.concat "," parents))
          a.boolean_steps
  in
  String.concat "\n" (sources @ input_groups @ component_definitions @ steps @ boolean_steps)

type token =
  | Name of string
  | Quoted of string
  | Variable of string
  | Number of string
  | Op of string

let lex text =
  let n = String.length text and i = ref 0 and tokens = ref [] in
  let add t = tokens := t :: !tokens in
  let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  let is_digit c = c >= '0' && c <= '9' in
  let rec whitespace () =
    if !i < n then
      match text.[!i] with
      | ' ' | '\n' | '\r' | '\t' ->
          incr i;
          whitespace ()
      | '%' ->
          while !i < n && text.[!i] <> '\n' do
            incr i
          done;
          whitespace ()
      | '/' when !i + 1 < n && text.[!i + 1] = '*' ->
          i := !i + 2;
          while !i + 1 < n && not (text.[!i] = '*' && text.[!i + 1] = '/') do
            incr i
          done;
          if !i + 1 >= n then raise (Error "unclosed block comment");
          i := !i + 2;
          whitespace ()
      | _ -> ()
  in
  whitespace ();
  while !i < n do
    let c = text.[!i] in
    (if c = '\'' then (
       incr i;
       let b = Buffer.create 16 in
       let rec chars () =
         if !i >= n then raise (Error "unclosed quoted atom");
         let c = text.[!i] in
         incr i;
         if c = '\'' then ()
         else if c = '\\' then (
           if !i >= n || not (List.mem text.[!i] [ '\\'; '\'' ]) then
             raise (Error "invalid quoted escape");
           Buffer.add_char b text.[!i];
           incr i;
           chars ())
         else (
           Buffer.add_char b c;
           chars ())
       in
       chars ();
       add (Quoted (Buffer.contents b)))
     else if is_letter c || c = '_' || c = '$' || is_digit c then (
       let start = !i in
       incr i;
       while
         !i < n && (is_letter text.[!i] || is_digit text.[!i] || text.[!i] = '_' || text.[!i] = '$')
       do
         incr i
       done;
       let word = String.sub text start (!i - start) in
       add
         (if (c >= 'A' && c <= 'Z') || c = '_' then Variable word
          else if is_digit c then Number word
          else Name word))
     else
       let candidates = [ "<=>"; "<~>"; "=>"; "<="; "!="; "~&"; "~|" ] in
       match
         List.find_opt
           (fun op ->
             let len = String.length op in
             !i + len <= n && String.sub text !i len = op)
           candidates
       with
       | Some op ->
           i := !i + String.length op;
           add (Op op)
       | None ->
           if not (List.mem c [ '('; ')'; '['; ']'; ','; '.'; ':'; '!'; '?'; '~'; '&'; '|'; '=' ])
           then raise (Error ("unsupported TPTP character: " ^ String.make 1 c));
           incr i;
           add (Op (String.make 1 c)));
    whitespace ()
  done;
  Array.of_list (List.rev !tokens)

let parse_annotated text =
  let tokens = lex text and pos = ref 0 in
  let peek () = if !pos = Array.length tokens then None else Some tokens.(!pos) in
  let take () =
    match peek () with
    | None -> raise (Error "unexpected end of TPTP input")
    | Some x ->
        incr pos;
        x
  in
  let accept s =
    if peek () = Some (Op s) then (
      incr pos;
      true)
    else false
  in
  let expect s =
    if not (accept s) then raise (Error ("expected '" ^ s ^ "' at token " ^ string_of_int !pos))
  in
  let symbol () =
    match take () with Name s | Quoted s -> s | _ -> raise (Error "expected an atomic name")
  in
  let functions = Hashtbl.create 16 and predicates = Hashtbl.create 16 in
  let declare table s arity =
    match Hashtbl.find_opt table s with
    | None -> Hashtbl.add table s arity
    | Some n when n = arity -> ()
    | Some _ -> raise (Error ("symbol arity overloading is not supported: " ^ s))
  in
  let fresh = ref 0 and frees = Hashtbl.create 16 in
  let variable env name =
    let rec index i = function
      | [] -> None
      | x :: xs -> if x = name then Some i else index (i + 1) xs
    in
    match index 0 env with
    | Some i -> B i
    | None ->
        let id =
          match Hashtbl.find_opt frees name with
          | Some i -> i
          | None ->
              let i = !fresh in
              incr fresh;
              Hashtbl.add frees name i;
              i
        in
        F id
  in
  let rec raw_term ?(depth = 0) env =
    if depth > 256 then raise (Error "TPTP term nesting limit");
    match take () with
    | Variable s -> variable env s
    | (Name s | Quoted s) as tok ->
        (match tok with
        | Name s when String.starts_with ~prefix:"$" s ->
            raise (Error "interpreted TPTP symbols are not supported")
        | _ -> ());
        let ts =
          if accept "(" then
            let x = raw_term ~depth:(depth + 1) env in
            let rec args acc =
              if accept "," then
                let x = raw_term ~depth:(depth + 1) env in
                args (x :: acc)
              else (
                expect ")";
                List.rev acc)
            in
            args [ x ]
          else []
        in
        App (s, ts)
    | _ -> raise (Error "expected an uninterpreted first-order term")
  in
  let rec register_term = function
    | B _ | F _ -> ()
    | App (f, ts) ->
        declare functions f (List.length ts);
        List.iter register_term ts
  in
  let rec formula env depth =
    if depth > 256 then raise (Error "TPTP nesting limit");
    let x = unit_formula env (depth + 1) in
    let connective =
      match peek () with
      | Some (Op (("&" | "|" | "=>" | "<=" | "<=>" | "<~>" | "~&" | "~|") as s)) -> Some s
      | _ -> None
    in
    match connective with
    | None -> x
    | Some op ->
        ignore (take ());
        let y = unit_formula env (depth + 1) in
        let result =
          match op with
          | "&" | "|" ->
              let rec rest acc =
                if accept op then
                  let z = unit_formula env (depth + 1) in
                  rest (z :: acc)
                else List.rev acc
              in
              let fs = rest [ y; x ] in
              if op = "&" then Conj fs else Disj fs
          | "=>" -> Disj [ Neg x; y ]
          | "<=" -> Disj [ x; Neg y ]
          | "<=>" -> Conj [ Disj [ Neg x; y ]; Disj [ Neg y; x ] ]
          | "<~>" -> Neg (Conj [ Disj [ Neg x; y ]; Disj [ Neg y; x ] ])
          | "~&" -> Neg (Conj [ x; y ])
          | "~|" -> Neg (Disj [ x; y ])
          | _ -> assert false
        in
        (match peek () with
        | Some (Op ("&" | "|" | "=>" | "<=" | "<=>" | "<~>" | "~&" | "~|")) ->
            raise (Error "mixed or chained binary connectives need parentheses")
        | _ -> ());
        result
  and unit_formula env depth =
    if depth > 256 then raise (Error "TPTP nesting limit");
    if accept "(" then (
      let f = formula env (depth + 1) in
      expect ")";
      f)
    else if accept "~" then Neg (unit_formula env (depth + 1))
    else if peek () = Some (Op "!") || peek () = Some (Op "?") then (
      let universal = take () = Op "!" in
      expect "[";
      let binder () =
        match take () with Variable s -> s | _ -> raise (Error "quantifier requires variables")
      in
      let x = binder () in
      let rec vars acc =
        if accept "," then
          let x = binder () in
          vars (x :: acc)
        else (
          expect "]";
          List.rev acc)
      in
      let vars = vars [ x ] in
      if List.length vars <> List.length (List.sort_uniq compare vars) then
        raise (Error "duplicate quantifier variable");
      expect ":";
      let f = unit_formula (List.rev vars @ env) (depth + 1) in
      List.fold_right (fun _ f -> if universal then All f else Ex f) vars f)
    else
      match peek () with
      | Some (Name "$true") ->
          ignore (take ());
          Top
      | Some (Name "$false") ->
          ignore (take ());
          Bot
      | _ -> (
          let x = raw_term env in
          if peek () = Some (Op "=") || peek () = Some (Op "!=") then (
            let positive = take () = Op "=" in
            let y = raw_term env in
            register_term x;
            register_term y;
            if positive then Eq (x, y) else Neg (Eq (x, y)))
          else
            match x with
            | App (p, ts) ->
                declare predicates p (List.length ts);
                List.iter register_term ts;
                Pred (p, ts)
            | _ -> raise (Error "a term variable is not a proposition"))
  in
  let rec cnf = function
    | Pred _ | Eq _ | Top | Bot | Neg (Pred _ | Eq _ | Top | Bot) -> true
    | Disj fs -> List.for_all cnf fs
    | _ -> false
  in
  let rec entries acc =
    match peek () with
    | None -> List.rev acc
    | Some _ ->
        let language = symbol () in
        if language <> "fof" && language <> "cnf" then
          raise (Error "only FOF/CNF declarations are supported (no include/TFF/THF)");
        expect "(";
        let name =
          match take () with
          | Name s | Quoted s | Number s -> s
          | _ -> raise (Error "invalid formula name")
        in
        expect ",";
        let role = symbol () in
        if
          not
            (List.mem role
               [ "axiom"; "hypothesis"; "definition"; "assumption"; "negated_conjecture" ])
        then raise (Error ("unsupported formula role: " ^ role));
        expect ",";
        Hashtbl.clear frees;
        fresh := 0;
        let f = formula [] 0 in
        if language = "fof" && Hashtbl.length frees <> 0 then
          raise (Error "FOF formula has an unbound variable");
        if language = "cnf" && not (cnf f) then raise (Error "CNF declaration is not a clause");
        expect ")";
        expect ".";
        entries ((name, role, f) :: acc)
  in
  let formulas = entries [] in
  let pairs t = Hashtbl.fold (fun s n xs -> (s, n) :: xs) t [] in
  ( Theory.custom ~name:"tptp"
      (Signature.make ~functions:(pairs functions) ~predicates:(pairs predicates))
      (List.map (fun (name, _, f) -> (name, f)) formulas),
    List.map (fun (name, role, _) -> (name, role)) formulas )

(* Roles are search annotations only. They never enter the manifest or a
   certificate: the kernel checks the same Source axioms whatever their role. *)
let parse text = fst (parse_annotated text)
let load path = Sexp.read_file path |> parse
