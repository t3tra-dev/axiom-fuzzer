type t = { functions : (string * int) list; predicates : (string * int) list; unrestricted : bool }

let validate xs =
  let seen = Hashtbl.create 16 in
  List.iter
    (fun (s, n) ->
      if s = "" || n < 0 || Hashtbl.mem seen s then
        invalid_arg "Signature: invalid or duplicate symbol";
      Hashtbl.add seen s ())
    xs;
  List.sort compare xs

let make ~functions ~predicates =
  { functions = validate functions; predicates = validate predicates; unrestricted = false }

let unrestricted = { functions = []; predicates = []; unrestricted = true }
let is_unrestricted s = s.unrestricted
let sets = make ~functions:[] ~predicates:[ ("member", 2) ]
let functions s = s.functions
let predicates s = s.predicates

let check symbols s n =
  if List.assoc_opt s symbols <> Some n then
    invalid_arg ("Signature: unknown symbol or wrong arity: " ^ s)

let check_open _ n = if n < 0 then invalid_arg "Signature: negative arity"
let check_function t = if t.unrestricted then check_open else check t.functions
let check_predicate t = if t.unrestricted then check_open else check t.predicates
