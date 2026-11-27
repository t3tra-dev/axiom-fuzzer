open Wire
open Sexp

let tag s xs = List (Atom s :: xs)
let number n = Atom (string_of_int n)
let flag b = Atom (if b then "+" else "-")
let var (s, i) = List [ number s; number i ]

let symbol = function
  | Original s -> tag "original" [ Atom s ]
  | Skolem (a, i) -> tag "skolem" [ number a; number i ]

let rec term = function
  | V v -> tag "var" [ var v ]
  | Fn (s, ts) -> tag "fun" [ symbol s; List (List.map term ts) ]

let atom = function
  | P (s, ts) -> tag "pred" [ Atom s; List (List.map term ts) ]
  | E (x, y) -> tag "eq" [ term x; term y ]
  | D ((a, i), ts) -> tag "definition" [ number a; number i; List (List.map term ts) ]

let literal l = List [ flag l.positive; atom l.atom ]
let clause c = List (List.map literal c)
let subst s = List (List.map (fun (v, t) -> List [ var v; term t ]) s)

let rec source_term = function
  | B i -> tag "bound" [ number i ]
  | F i -> tag "free" [ number i ]
  | App (s, ts) -> tag "app" [ Atom s; List (List.map source_term ts) ]

let rec source = function
  | Top -> tag "true" []
  | Bot -> tag "false" []
  | Pred (s, ts) -> tag "pred" [ Atom s; List (List.map source_term ts) ]
  | Eq (x, y) -> tag "eq" [ source_term x; source_term y ]
  | Neg f -> tag "not" [ source f ]
  | Conj fs -> tag "and" (List.map source fs)
  | Disj fs -> tag "or" (List.map source fs)
  | All f -> tag "all" [ source f ]
  | Ex f -> tag "exists" [ source f ]

let schema = Wire.schema_name

let schema_id = function
  | Registered (name, revision) -> tag "registered" [ Atom name; Atom revision ]
  | s -> Atom (schema s)

let origin = function
  | Fixed s -> tag "fixed" [ Atom s ]
  | Imported s -> tag "imported" [ Atom s ]
  | Instance (Registered _, _) -> invalid_arg "registered schema requires encoded parameters"
  | Instance (s, f) -> tag "schema" [ Atom (schema s); source f ]
  | Registered_instance (name, revision, data) ->
      tag "registered-schema" [ Atom name; Atom revision; Atom data ]

let axiom a = List [ number a.axiom_id; Atom a.name; origin a.origin; source a.formula ]

let rule = function
  | Input (a, i) -> tag "input" [ number a; number i ]
  | Component id -> tag "component" [ number id ]
  | Resolve (p, i, q, j, s) -> tag "resolve" [ number p; number i; number q; number j; subst s ]
  | Factor (p, i, j, s) -> tag "factor" [ number p; number i; number j; subst s ]
  | Equality_resolve (p, i, s) -> tag "equality-resolve" [ number p; number i; subst s ]
  | Equality_factor (p, i, r, j, q, s) ->
      tag "equality-factor" [ number p; number i; flag r; number j; flag q; subst s ]
  | Paramodulate (p, i, r, q, j, path, s) ->
      tag "paramodulate"
        [ number p; number i; flag r; number q; number j; List (List.map number path); subst s ]

let rec code = function Wire_types.Number n -> number n | Pair (x, y) -> List [ code x; code y ]

let boolean_rule = function
  | Split id -> tag "split" [ number id ]
  | Conflict id -> tag "conflict" [ number id ]
  | Boolean_resolve (p, pivot, q) -> tag "boolean-resolve" [ number p; number pivot; number q ]

let avatar a =
  tag "avatar"
    [
      List (List.map clause a.components);
      List (List.map (fun (p, ids) -> List [ number p; List (List.map number ids) ]) a.splits);
      List
        (List.map
           (fun s ->
             List
               [
                 number s.boolean_id;
                 List (List.map number s.boolean_clause);
                 boolean_rule s.boolean_rule;
               ])
           a.boolean_steps);
      number a.boolean_root;
    ]

let output ~char ~string c =
  if Option.is_some c.natural && Option.is_some c.avatar then
    invalid_arg "mixed natural and AVATAR certificate";
  let value = Sexp.output ~char ~string in
  let field emit x =
    char ' ';
    emit x
  in
  let sequence emit xs =
    char '(';
    List.iteri
      (fun i x ->
        if i > 0 then char ' ';
        emit x)
      xs;
    char ')'
  in
  let tagged name body =
    char '(';
    value (Atom name);
    body ();
    char ')'
  in
  let rec natural = function
    | Wire_types.Number n -> value (number n)
    | Pair (x, y) ->
        char '(';
        natural x;
        field natural y;
        char ')'
  in
  let emit_avatar a =
    tagged "avatar" (fun () ->
        field (sequence (fun c -> value (clause c))) a.components;
        field
          (sequence (fun (p, ids) -> value (List [ number p; List (List.map number ids) ])))
          a.splits;
        field
          (sequence (fun s ->
               value
                 (List
                    [
                      number s.boolean_id;
                      List (List.map number s.boolean_clause);
                      boolean_rule s.boolean_rule;
                    ])))
          a.boolean_steps;
        field value (number a.boolean_root))
  in
  (* Keep only one axiom/step's structural view at a time. The canonical text
     stays identical without a complete S-expression copy of the proof DAG. *)
  tagged "axiom-fuzzer" (fun () ->
      field value (Atom c.theory);
      match c.natural with
      | Some proof ->
          char ' ';
          tagged "natural" (fun () -> field natural proof)
      | None ->
          field value (tag "cnf" [ Atom (cnf_mode_name c.cnf_mode) ]);
          field (sequence (fun a -> value (axiom a))) c.axioms;
          field
            (sequence (fun (s : step) -> value (List [ number s.id; clause s.clause; rule s.rule ])))
            c.steps;
          field value (number c.root);
          Option.iter (field emit_avatar) c.avatar)

let encode c =
  let buffer = Buffer.create 4096 in
  output ~char:(Buffer.add_char buffer) ~string:(Buffer.add_string buffer) c;
  Buffer.contents buffer

let error () = raise (Sexp.Error "invalid certificate structure")
let str = function Atom s -> s | _ -> error ()

let int x =
  try
    let n = int_of_string (str x) in
    if n < 0 then error ();
    n
  with Failure _ -> error ()

let bool = function Atom "+" -> true | Atom "-" -> false | _ -> error ()
let list f = function List xs -> List.map f xs | _ -> error ()
let variable = function List [ s; i ] -> (int s, int i) | _ -> error ()

let decode_symbol = function
  | List [ Atom "original"; s ] -> Original (str s)
  | List [ Atom "skolem"; a; i ] -> Skolem (int a, int i)
  | _ -> error ()

let rec decode_term = function
  | List [ Atom "var"; v ] -> V (variable v)
  | List [ Atom "fun"; s; ts ] -> Fn (decode_symbol s, list decode_term ts)
  | _ -> error ()

let decode_atom = function
  | List [ Atom "pred"; s; ts ] -> P (str s, list decode_term ts)
  | List [ Atom "definition"; a; i; ts ] -> D ((int a, int i), list decode_term ts)
  | List [ Atom "eq"; x; y ] -> E (decode_term x, decode_term y)
  | _ -> error ()

let decode_lit = function
  | List [ p; a ] -> { positive = bool p; atom = decode_atom a }
  | _ -> error ()

let decode_subst = list (function List [ v; t ] -> (variable v, decode_term t) | _ -> error ())

let rec decode_source_term = function
  | List [ Atom "bound"; i ] -> B (int i)
  | List [ Atom "free"; i ] -> F (int i)
  | List [ Atom "app"; s; ts ] -> App (str s, list decode_source_term ts)
  | _ -> error ()

let rec decode_source = function
  | List [ Atom "true" ] -> Top
  | List [ Atom "false" ] -> Bot
  | List [ Atom "pred"; s; ts ] -> Pred (str s, list decode_source_term ts)
  | List [ Atom "eq"; x; y ] -> Eq (decode_source_term x, decode_source_term y)
  | List [ Atom "not"; f ] -> Neg (decode_source f)
  | List (Atom "and" :: fs) -> Conj (List.map decode_source fs)
  | List (Atom "or" :: fs) -> Disj (List.map decode_source fs)
  | List [ Atom "all"; f ] -> All (decode_source f)
  | List [ Atom "exists"; f ] -> Ex (decode_source f)
  | _ -> error ()

let decode_schema = function
  | Atom "comprehension" -> Comprehension
  | Atom "separation" -> Separation
  | Atom "replacement" -> Replacement
  | Atom "unrestricted-separation" -> Unrestricted_separation
  | _ -> error ()

let decode_origin = function
  | List [ Atom "fixed"; s ] -> Fixed (str s)
  | List [ Atom "imported"; s ] -> Imported (str s)
  | List [ Atom "schema"; s; f ] -> Instance (decode_schema s, decode_source f)
  | List [ Atom "registered-schema"; name; revision; data ] ->
      Registered_instance (str name, str revision, str data)
  | _ -> error ()

let decode_axiom = function
  | List [ id; name; o; f ] ->
      { axiom_id = int id; name = str name; origin = decode_origin o; formula = decode_source f }
  | _ -> error ()

let decode_rule = function
  | List [ Atom "input"; a; i ] -> Input (int a, int i)
  | List [ Atom "component"; id ] -> Component (int id)
  | List [ Atom "resolve"; p; i; q; j; s ] -> Resolve (int p, int i, int q, int j, decode_subst s)
  | List [ Atom "factor"; p; i; j; s ] -> Factor (int p, int i, int j, decode_subst s)
  | List [ Atom "equality-resolve"; p; i; s ] -> Equality_resolve (int p, int i, decode_subst s)
  | List [ Atom "equality-factor"; p; i; r; j; q; s ] ->
      Equality_factor (int p, int i, bool r, int j, bool q, decode_subst s)
  | List [ Atom "paramodulate"; p; i; r; q; j; path; s ] ->
      Paramodulate (int p, int i, bool r, int q, int j, list int path, decode_subst s)
  | _ -> error ()

let decode_step = function
  | List [ id; c; r ] -> { id = int id; clause = list decode_lit c; rule = decode_rule r }
  | _ -> error ()

let rec decode_code = function
  | Atom _ as x -> Wire_types.Number (int x)
  | List [ x; y ] -> Pair (decode_code x, decode_code y)
  | _ -> error ()

let decode_avatar = function
  | List [ Atom "avatar"; components; splits; steps; root ] ->
      let signed x =
        try
          let n = int_of_string (str x) in
          if n = 0 || n = min_int then error ();
          n
        with Failure _ -> error ()
      in
      let rule = function
        | List [ Atom "split"; i ] -> Split (int i)
        | List [ Atom "conflict"; i ] -> Conflict (int i)
        | List [ Atom "boolean-resolve"; p; pivot; q ] -> Boolean_resolve (int p, int pivot, int q)
        | _ -> error ()
      in
      {
        components = list (list decode_lit) components;
        splits = list (function List [ p; ids ] -> (int p, list int ids) | _ -> error ()) splits;
        boolean_steps =
          list
            (function
              | List [ id; clause; r ] ->
                  {
                    boolean_id = int id;
                    boolean_clause = list signed clause;
                    boolean_rule = rule r;
                  }
              | _ -> error ())
            steps;
        boolean_root = int root;
      }
  | _ -> error ()

let decode text =
  match Sexp.parse text with
  | List [ Atom "axiom-fuzzer"; t; List [ Atom "natural"; proof ] ] ->
      {
        natural = Some (decode_code proof);
        avatar = None;
        theory = str t;
        cnf_mode = Hybrid;
        axioms = [];
        steps = [];
        root = 0;
      }
  | List (Atom "axiom-fuzzer" :: t :: List [ Atom "cnf"; mode ] :: axs :: steps :: root :: rest)
    when List.length rest <= 1 ->
      {
        natural = None;
        avatar = (match rest with [] -> None | [ a ] -> Some (decode_avatar a) | _ -> error ());
        cnf_mode = cnf_mode_of_string (str mode);
        theory = str t;
        axioms = list decode_axiom axs;
        steps = list decode_step steps;
        root = int root;
      }
  | _ -> error ()

let read path = Sexp.read_file path |> decode

let write path c =
  Sexp.write_file_with path (fun channel ->
      output ~char:(output_char channel) ~string:(output_string channel) c)
