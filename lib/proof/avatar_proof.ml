open Wire

(* Portable metadata reconstruction and proof slicing. This is not the trusted
   acceptance boundary: Kernel also runs the independently extracted checker. *)

let require condition message = if not condition then invalid_arg ("AVATAR: " ^ message)
let canonical xs = List.sort_uniq compare xs

(* Propose the variable instance that aligns a split occurrence with shared
   representatives. The primitive checker independently checks this instance,
   literal coverage and disjointness; this matcher is not trusted. *)
let split_substitution ?(guard = fun () -> ()) parent parts =
  let used = ref [] in
  let bindings =
    Clause.components ~guard parent
    |> List.concat_map (fun occurrence ->
        guard ();
        match
          List.find_map
            (fun (i, representative) ->
              Option.map
                (fun renaming -> (i, renaming))
                (Variant_index.renaming occurrence representative))
            (List.mapi (fun i c -> (i, c)) parts)
        with
        | None -> invalid_arg "AVATAR: split does not cover a variable-disjoint component"
        | Some (i, renaming) ->
            used := i :: !used;
            List.map (fun (x, y) -> (x, V y)) renaming)
  in
  require (List.length (canonical !used) = List.length parts) "unused split component";
  bindings

let component_of_literal literal =
  require (literal <> 0 && literal <> min_int) "invalid Boolean literal";
  abs literal - 1

let dependencies steps =
  let supports = Hashtbl.create 128 in
  List.iter
    (fun (step : step) ->
      require (step.id >= 0 && not (Hashtbl.mem supports step.id)) "duplicate FO step";
      let support =
        match step.rule with
        | Input _ -> []
        | Component id ->
            require (id >= 0) "negative component";
            [ id ]
        | rule ->
            List.concat_map
              (fun parent ->
                require (parent >= 0 && parent < step.id) "future FO parent";
                match Hashtbl.find_opt supports parent with
                | Some support -> support
                | None -> invalid_arg "AVATAR: missing FO parent")
              (parents rule)
            |> canonical
      in
      Hashtbl.add supports step.id support)
    steps;
  fun id ->
    match Hashtbl.find_opt supports id with
    | Some support -> support
    | None -> invalid_arg "AVATAR: missing FO dependency"

let validate ?(guard = fun () -> ()) steps avatar =
  let support = dependencies steps in
  let components = Array.of_list avatar.components in
  let component id =
    require (id >= 0 && id < Array.length components) "unknown component";
    components.(id)
  in
  let nodes = Hashtbl.create 128 in
  List.iter (fun (s : step) -> Hashtbl.add nodes s.id s.clause) steps;
  let parent id =
    match Hashtbl.find_opt nodes id with
    | Some c -> c
    | None -> invalid_arg "AVATAR: missing FO leaf"
  in
  let negate id =
    ignore (component id);
    -(id + 1)
  in
  let splits =
    Array.of_list
      (List.map
         (fun (id, ids) ->
           guard ();
           let used = ref [] in
           let parts =
             List.map
               (fun cid ->
                 let c = component cid in
                 let variables = variables c in
                 require
                   (List.for_all (fun v -> not (List.mem v !used)) variables)
                   "split components share variables";
                 used := variables @ !used;
                 c)
               ids
           in
           ignore (split_substitution ~guard (parent id) parts);
           canonical (List.map negate (support id) @ List.map (fun i -> i + 1) ids))
         avatar.splits)
  in
  let boolean = Hashtbl.create 128 in
  List.iter
    (fun s ->
      guard ();
      require (s.boolean_id >= 0 && not (Hashtbl.mem boolean s.boolean_id)) "duplicate Boolean step";
      List.iter (fun literal -> ignore (component (component_of_literal literal))) s.boolean_clause;
      let previous id =
        require (id >= 0 && id < s.boolean_id) "future Boolean parent";
        match Hashtbl.find_opt boolean id with
        | Some c -> c
        | None -> invalid_arg "AVATAR: missing Boolean parent"
      in
      let expected =
        match s.boolean_rule with
        | Split i ->
            require (i >= 0 && i < Array.length splits) "unknown split";
            splits.(i)
        | Conflict id ->
            require (parent id = []) "conflict does not refer to an empty FO clause";
            List.map negate (support id)
        | Boolean_resolve (p, pivot, q) ->
            ignore (component pivot);
            let x = pivot + 1 and left = previous p and right = previous q in
            let sign =
              if List.mem x left && List.mem (-x) right then x
              else if List.mem (-x) left && List.mem x right then -x
              else invalid_arg "AVATAR: Boolean pivots are not complementary"
            in
            List.filter (( <> ) sign) left @ List.filter (( <> ) (-sign)) right
      in
      require (canonical expected = canonical s.boolean_clause) "Boolean conclusion mismatch";
      Hashtbl.add boolean s.boolean_id (canonical s.boolean_clause))
    avatar.boolean_steps;
  require (Hashtbl.find_opt boolean avatar.boolean_root = Some []) "Boolean root is not empty";
  support

let prune (certificate : certificate) avatar =
  let booleans = Hashtbl.create 128 and kept_booleans = Hashtbl.create 128 in
  List.iter (fun s -> Hashtbl.add booleans s.boolean_id s) avatar.boolean_steps;
  let splits = Array.of_list avatar.splits and needed_splits = Hashtbl.create 32 in
  let roots = ref [] and components = Hashtbl.create 32 in
  let keep_component id = Hashtbl.replace components id () in
  let rec visit_boolean id =
    if not (Hashtbl.mem kept_booleans id) then (
      let s = Hashtbl.find booleans id in
      Hashtbl.add kept_booleans id ();
      List.iter (fun l -> keep_component (component_of_literal l)) s.boolean_clause;
      match s.boolean_rule with
      | Split i ->
          Hashtbl.replace needed_splits i ();
          let parent, ids = splits.(i) in
          roots := parent :: !roots;
          List.iter keep_component ids
      | Conflict id -> roots := id :: !roots
      | Boolean_resolve (p, pivot, q) ->
          keep_component pivot;
          visit_boolean p;
          visit_boolean q)
  in
  visit_boolean avatar.boolean_root;
  let fo = Hashtbl.create 128 and kept_fo = Hashtbl.create 128 in
  List.iter (fun (s : step) -> Hashtbl.add fo s.id s) certificate.steps;
  let rec visit_fo id =
    if not (Hashtbl.mem kept_fo id) then (
      let s = Hashtbl.find fo id in
      Hashtbl.add kept_fo id ();
      (match s.rule with Component id -> keep_component id | _ -> ());
      List.iter visit_fo (parents s.rule))
  in
  List.iter visit_fo !roots;
  let component_ids = Hashtbl.create 32 and split_ids = Hashtbl.create 32 in
  let components =
    List.filter_map
      (fun (id, c) ->
        if Hashtbl.mem components id then (
          Hashtbl.add component_ids id (Hashtbl.length component_ids);
          Some c)
        else None)
      (List.mapi (fun i c -> (i, c)) avatar.components)
  in
  let remap = Hashtbl.find component_ids in
  let splits =
    List.filter_map
      (fun (i, (parent, ids)) ->
        if Hashtbl.mem needed_splits i then (
          Hashtbl.add split_ids i (Hashtbl.length split_ids);
          Some (parent, List.map remap ids))
        else None)
      (List.mapi (fun i s -> (i, s)) avatar.splits)
  in
  let steps =
    List.filter_map
      (fun (s : step) ->
        if Hashtbl.mem kept_fo s.id then
          Some { s with rule = (match s.rule with Component id -> Component (remap id) | r -> r) }
        else None)
      certificate.steps
  in
  let boolean_steps =
    List.filter_map
      (fun s ->
        if not (Hashtbl.mem kept_booleans s.boolean_id) then None
        else
          let literal l =
            let id = remap (component_of_literal l) + 1 in
            if l > 0 then id else -id
          in
          let boolean_rule =
            match s.boolean_rule with
            | Split i -> Split (Hashtbl.find split_ids i)
            | Conflict _ as r -> r
            | Boolean_resolve (p, pivot, q) -> Boolean_resolve (p, remap pivot, q)
          in
          Some { s with boolean_clause = List.map literal s.boolean_clause; boolean_rule })
      avatar.boolean_steps
  in
  { certificate with steps; avatar = Some { avatar with components; splits; boolean_steps } }
