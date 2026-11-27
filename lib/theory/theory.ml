open Source

module Schema = struct
  type bounds = { max_size : int; parameters : int }

  type 'p t = {
    key : Wire.schema;
    encode : 'p -> string;
    decode : string -> 'p option;
    enumerate : Signature.t -> bounds option -> 'p option Seq.t;
    expand : Source.t -> 'p -> Source.formula;
    check : Signature.t -> 'p -> Wire.source -> bool;
    guide : Source.t -> Source.formula -> 'p option;
  }

  let create ?(guide = fun _ _ -> None) ~name ~revision ~encode ~decode ~enumerate ~expand ~check ()
      =
    if name = "" || revision = "" then invalid_arg "Schema: empty name or revision";
    {
      key = Wire.Registered (name, revision);
      encode;
      decode;
      enumerate = (fun signature bounds -> Seq.map Option.some (enumerate signature bounds));
      expand;
      check;
      guide;
    }

  let key s = s.key
end

type parameter = Formula of Source.formula | Data of string

type registration = {
  key : Wire.schema;
  enumerate : Source.t -> Schema.bounds option -> parameter option Seq.t;
  expand : Source.t -> string -> Source.formula;
  check : Signature.t -> string -> Wire.source -> bool;
  guide : Source.t -> Source.formula -> parameter option;
}

type t = { manifest : Source_checker.theory; arena : Source.t; registered : registration list }

let manifest t = t.manifest
let name t = t.manifest.theory_name
let arena t = t.arena
let fixed t = t.manifest.fixed_axioms
let schemas t = t.manifest.allowed_schemas

(* Immutable manifests may be shared; Source hash-cons arenas must not be. *)
let copy ?(preserve_arena = false) t =
  {
    t with
    arena =
      (if preserve_arena then Source.copy t.arena else Source.create (Source.signature t.arena));
  }

let names =
  [ "naive"; "separation"; "separation-universal"; "foundation-self"; "mutated-separation"; "zf" ]

let arity = function
  | Wire.Replacement -> 2
  | Registered _ -> invalid_arg "Theory: registered schemas have their own parameter type"
  | _ -> 1

let schema_name = Wire.schema_name

let registration t key =
  match List.find_opt (fun r -> r.key = key) t.registered with
  | Some r -> r
  | None -> invalid_arg "Theory: schema name/revision not registered"

let make_manifest ~name signature fixed schemas registered =
  let registered_check name revision data formula =
    match List.find_opt (fun r -> r.key = Wire.Registered (name, revision)) registered with
    | None -> false
    | Some r -> r.check signature data formula
  in
  {
    Source_checker.theory_name = name;
    unrestricted_signature = Signature.is_unrestricted signature;
    function_symbols = Signature.functions signature;
    predicate_symbols = Signature.predicates signature;
    fixed_axioms = fixed;
    allowed_schemas = schemas;
    registered_check;
  }

let register_schema t (s : 'p Schema.t) =
  let name = schema_name s.key in
  let reserved = [ Wire.Comprehension; Separation; Replacement; Unrestricted_separation ] in
  if List.exists (fun key -> schema_name key = name) (reserved @ t.manifest.allowed_schemas) then
    invalid_arg "Theory: duplicate or reserved schema name";
  let decode data =
    match s.decode data with
    | Some p when s.encode p = data -> p
    | _ -> invalid_arg "Schema: invalid or noncanonical parameter encoding"
  in
  let encode p =
    let data = s.encode p in
    ignore (decode data);
    Data data
  in
  let r =
    {
      key = s.key;
      enumerate =
        (fun a bounds -> Seq.map (Option.map encode) (s.enumerate (Source.signature a) bounds));
      expand = (fun a data -> s.expand a (decode data));
      check =
        (fun signature data formula ->
          match s.decode data with
          | Some p when s.encode p = data -> s.check signature p formula
          | _ -> false);
      guide = (fun a phi -> Option.map encode (s.guide a phi));
    }
  in
  let registered = t.registered @ [ r ] in
  let manifest =
    make_manifest ~name:t.manifest.theory_name (Source.signature t.arena) (fixed t)
      (schemas t @ [ s.key ])
      registered
  in
  { t with manifest; registered }

let schema_parameters a schema phi =
  if not (well_scoped a ~depth:0 phi) then invalid_arg "Schema: open bound variable";
  let arity = arity schema in
  let params = List.filter (fun i -> i >= arity) (free_vars a phi) in
  let maximum = List.fold_left max (arity - 1) params in
  let reserved = if schema = Wire.Replacement then 3 else 2 in
  if maximum > max_int - reserved then invalid_arg "Schema: no fresh variable index available";
  (params, maximum + 1)

let schema_formula a schema phi =
  let params, fresh = schema_parameters a schema phi in
  let av = fresh and bv = fresh + 1 in
  let x = free a 0 and y = free a 1 and set = free a av and result = free a bv in
  let finish f = all a params f in
  match schema with
  | Wire.Comprehension | Unrestricted_separation ->
      finish (ex a [ bv ] (all a [ 0 ] (iff a (member a x result) phi)))
  | Separation ->
      finish
        (all a [ av ]
           (ex a [ bv ] (all a [ 0 ] (iff a (member a x result) (and_ a [ member a x set; phi ])))))
  | Replacement ->
      let zv = fresh + 2 in
      let z = free a zv in
      let unique = all a [ zv ] (implies a (subst_free a 1 z phi) (eq a z y)) in
      let functional = all a [ 0 ] (ex a [ 1 ] (and_ a [ phi; unique ])) in
      let image =
        all a [ av ]
          (ex a [ bv ]
             (all a [ 1 ] (iff a (member a y result) (ex a [ 0 ] (and_ a [ member a x set; phi ])))))
      in
      finish (implies a functional image)
  | Registered _ -> invalid_arg "Theory: use instantiate_schema for registered parameters"

let instantiate t ~id schema phi =
  if id < 0 || not (List.mem schema t.manifest.allowed_schemas) then
    invalid_arg "Theory: schema not admitted";
  let f = schema_formula t.arena schema phi in
  if not (is_closed t.arena f) then invalid_arg "Theory: unclosed instance";
  {
    Wire.axiom_id = id;
    name = Printf.sprintf "%s_%d" (schema_name schema) id;
    origin = Wire.Instance (schema, Wire.export t.arena phi);
    formula = Wire.export t.arena f;
  }

let instantiate_parameter t ~id schema = function
  | Formula phi -> instantiate t ~id schema phi
  | Data data -> (
      if id < 0 then invalid_arg "Theory: negative axiom id";
      let r = registration t schema in
      let f = r.expand t.arena data in
      if not (is_closed t.arena f) then invalid_arg "Theory: unclosed instance";
      match schema with
      | Wire.Registered (name, revision) ->
          {
            Wire.axiom_id = id;
            name = Printf.sprintf "%s_%d" name id;
            origin = Wire.Registered_instance (name, revision, data);
            formula = Wire.export t.arena f;
          }
      | _ -> assert false)

let instantiate_schema t ~id (s : 'p Schema.t) p =
  instantiate_parameter t ~id s.key (Data (s.encode p))

let enumerate t ?bounds schema =
  if not (List.mem schema t.manifest.allowed_schemas) then invalid_arg "Theory: schema not admitted";
  Option.iter
    (fun (b : Schema.bounds) ->
      if b.max_size < 0 || b.parameters < 0 then invalid_arg "Theory: negative enumeration bound")
    bounds;
  match schema with
  | Wire.Registered _ -> (registration t schema).enumerate t.arena bounds
  | _ ->
      let seq =
        match bounds with
        | None -> Enumerate.exhaustive t.arena ~arity:(arity schema)
        | Some b ->
            Enumerate.bounded t.arena ~arity:(arity schema) ~parameters:b.parameters
              ~max_size:b.max_size
      in
      Seq.map (fun phi -> Some (Formula phi)) seq

let guided_parameter t schema phi =
  match schema with
  | Wire.Registered _ -> (registration t schema).guide t.arena phi
  | _ -> Some (Formula phi)

let parameter_info t schema = function
  | Formula phi ->
      let parameters =
        free_vars t.arena phi |> List.filter (fun v -> v >= arity schema) |> List.length
      in
      (Source.size t.arena phi, parameters)
  | Data _ -> (0, 0)

let parameter_text t = function Formula phi -> Source.to_string t.arena phi | Data data -> data

let fixed_formulas a =
  let v i = free a i in
  let mem x y = member a (v x) (v y) and equal x y = eq a (v x) (v y) in
  let ext = all a [ 0; 1 ] (implies a (all a [ 2 ] (iff a (mem 2 0) (mem 2 1))) (equal 0 1)) in
  let empty = ex a [ 0 ] (all a [ 1 ] (not_ a (mem 1 0))) in
  let pair =
    all a [ 0; 1 ] (ex a [ 2 ] (all a [ 3 ] (iff a (mem 3 2) (or_ a [ equal 3 0; equal 3 1 ]))))
  in
  let union =
    all a [ 0 ]
      (ex a [ 1 ] (all a [ 2 ] (iff a (mem 2 1) (ex a [ 3 ] (and_ a [ mem 3 0; mem 2 3 ])))))
  in
  let power =
    all a [ 0 ]
      (ex a [ 1 ] (all a [ 2 ] (iff a (mem 2 1) (all a [ 3 ] (implies a (mem 3 2) (mem 3 0))))))
  in
  let infinity =
    ex a [ 0 ]
      (and_ a
         [
           ex a [ 1 ] (and_ a [ all a [ 2 ] (not_ a (mem 2 1)); mem 1 0 ]);
           all a [ 1 ]
             (implies a (mem 1 0)
                (ex a [ 2 ]
                   (and_ a
                      [ mem 2 0; all a [ 3 ] (iff a (mem 3 2) (or_ a [ mem 3 1; equal 3 1 ])) ])));
         ])
  in
  let foundation =
    all a [ 0 ]
      (implies a
         (ex a [ 1 ] (mem 1 0))
         (ex a [ 1 ] (and_ a [ mem 1 0; all a [ 2 ] (implies a (mem 2 0) (not_ a (mem 2 1))) ])))
  in
  [
    ("extensionality", ext);
    ("empty", empty);
    ("pairing", pair);
    ("union", union);
    ("power", power);
    ("infinity", infinity);
    ("foundation", foundation);
    ("universal", ex a [ 0 ] (all a [ 1 ] (mem 1 0)));
    ("self-member", ex a [ 0 ] (mem 0 0));
  ]

let create name =
  let a = create Signature.sets in
  let all_fixed = fixed_formulas a in
  let selected, schemas =
    match name with
    | "naive" -> ([], [ Wire.Comprehension ])
    | "separation" -> ([], [ Wire.Separation ])
    | "separation-universal" -> ([ "universal" ], [ Wire.Separation ])
    | "foundation-self" -> ([ "pairing"; "foundation"; "self-member" ], [])
    | "mutated-separation" -> ([], [ Wire.Unrestricted_separation ])
    | "zf" ->
        ( [ "extensionality"; "empty"; "pairing"; "union"; "power"; "infinity"; "foundation" ],
          [ Wire.Separation; Wire.Replacement ] )
    | _ -> invalid_arg ("Unknown theory: " ^ name ^ " (known: " ^ String.concat ", " names ^ ")")
  in
  let fixed =
    List.mapi
      (fun id name ->
        {
          Wire.axiom_id = id;
          name;
          origin = Wire.Fixed name;
          formula = Wire.export a (List.assoc name all_fixed);
        })
      selected
  in
  {
    manifest = make_manifest ~name (Source.signature a) fixed schemas [];
    arena = a;
    registered = [];
  }

let custom ~name signature formulas =
  if List.mem name names then invalid_arg "Custom theory uses a reserved name";
  let a = Source.create signature in
  let seen = Hashtbl.create 16 in
  let fixed =
    List.mapi
      (fun id (name, f) ->
        if Hashtbl.mem seen name then invalid_arg "Duplicate axiom name";
        Hashtbl.add seen name ();
        let f = Wire.import a f |> close a in
        { Wire.axiom_id = id; name; origin = Wire.Imported name; formula = Wire.export a f })
      formulas
  in
  { manifest = make_manifest ~name signature fixed [] []; arena = a; registered = [] }

let of_definitions ~name definitions formulas =
  custom ~name
    (Definitions.base_signature definitions)
    (List.map (fun (label, formula) -> (label, Definitions.expand definitions formula)) formulas)

(* A total observation of an axiom enumeration. None is a quiet step, not the
   end of the stream. Its finite index is the authority witness in a proof. *)
let of_enumerator ~name ~revision ~step =
  let module N = Natural_checker in
  let step n =
    if n < 0 then invalid_arg "Theory: negative enumeration step";
    match step n with
    | Some f when not (Source_checker.formula_scoped 0 true f) ->
        invalid_arg "Theory: enumerator returned an open or malformed axiom"
    | result -> result
  in
  let decode text =
    (* Binary indices have at most this many value bits. Check before the
       extracted natural-number decoder can overflow a machine integer. *)
    if String.length text > Sys.int_size - 1 then None else N.index_value text
  in
  let prototype =
    Schema.create ~name:N.enumeration_name ~revision ~encode:N.index_text ~decode
      ~enumerate:(fun _ _ -> Seq.empty)
      ~expand:(fun arena n ->
        match step n with
        | Some f -> Wire.import arena f
        | None -> invalid_arg "Theory: no axiom at this enumeration step")
      ~check:(fun _ n f -> N.enumerated_check step (N.index_text n) f)
      ()
  in
  let enumerate _ bounds =
    let rec stages n () =
      match bounds with
      | Some (b : Schema.bounds) when n >= b.max_size -> Seq.Nil
      | _ ->
          let next () =
            if n = max_int then invalid_arg "Theory: enumeration machine integer limit";
            stages (n + 1) ()
          in
          Seq.Cons (Option.map (fun _ -> n) (step n), next)
    in
    stages 0
  in
  register_schema (custom ~name Signature.unrestricted []) { prototype with Schema.enumerate }

let instantiate_enumerated t ~id stage =
  if stage < 0 then invalid_arg "Theory: negative enumeration step";
  match
    List.find_opt
      (function Wire.Registered (name, _) -> name = Natural_checker.enumeration_name | _ -> false)
      (schemas t)
  with
  | None -> invalid_arg "Theory: no axiom enumerator registered"
  | Some key -> instantiate_parameter t ~id key (Data (Natural_checker.index_text stage))

let validate_axiom t (ax : Wire.axiom) =
  try
    let name_valid =
      match ax.origin with
      | Wire.Instance (schema, _) ->
          ax.name = Printf.sprintf "%s_%d" (schema_name schema) ax.axiom_id
      | Registered_instance (name, _, _) -> ax.name = Printf.sprintf "%s_%d" name ax.axiom_id
      | Fixed _ | Imported _ -> true
    in
    name_valid && Source_checker.validate_axiom max_int t.manifest ax
  with Invalid_argument _ -> false
