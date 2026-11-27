
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module Nat =
 struct
  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l' -> nth_error l' n0)
    n

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: l0 -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

module Sort =
 functor (X:TotalLeBool') ->
 struct
  (** val merge : X.t list -> X.t list -> X.t list **)

  let rec merge l1 l2 =
    let rec merge_aux l3 =
      match l1 with
      | [] -> l3
      | a1 :: l1' ->
        (match l3 with
         | [] -> l1
         | a2 :: l2' ->
           if X.leb a1 a2 then a1 :: (merge l1' l3) else a2 :: (merge_aux l2'))
    in merge_aux l2

  (** val merge_list_to_stack :
      X.t list option list -> X.t list -> X.t list option list **)

  let rec merge_list_to_stack stack l =
    match stack with
    | [] -> (Some l) :: []
    | y :: stack' ->
      (match y with
       | Some l' -> None :: (merge_list_to_stack stack' (merge l' l))
       | None -> (Some l) :: stack')

  (** val merge_stack : X.t list option list -> X.t list **)

  let rec merge_stack = function
  | [] -> []
  | y :: stack' ->
    (match y with
     | Some l -> merge l (merge_stack stack')
     | None -> merge_stack stack')

  (** val iter_merge : X.t list option list -> X.t list -> X.t list **)

  let rec iter_merge stack = function
  | [] -> merge_stack stack
  | a :: l' -> iter_merge (merge_list_to_stack stack (a :: [])) l'

  (** val sort : X.t list -> X.t list **)

  let sort =
    iter_merge []

  (** val flatten_stack : X.t list option list -> X.t list **)

  let rec flatten_stack = function
  | [] -> []
  | o :: stack' ->
    (match o with
     | Some l -> app l (flatten_stack stack')
     | None -> flatten_stack stack')
 end

(** val term_scoped : int -> bool -> 'a1 Wire_types.source_term -> bool **)

let rec term_scoped depth closed = function
| Wire_types.B i -> (&&) ((<=) 0 i) (negb ((<=) depth i))
| Wire_types.F i -> (&&) ((<=) 0 i) (negb closed)
| Wire_types.App (_, ts) -> forallb (term_scoped depth closed) ts

(** val formula_scoped :
    int -> bool -> ('a1, 'a2) Wire_types.source_formula -> bool **)

let rec formula_scoped depth closed = function
| Wire_types.Pred (_, ts) -> forallb (term_scoped depth closed) ts
| Wire_types.Eq (x, y) ->
  (&&) (term_scoped depth closed x) (term_scoped depth closed y)
| Wire_types.Neg f0 -> formula_scoped depth closed f0
| Wire_types.Conj fs -> forallb (formula_scoped depth closed) fs
| Wire_types.Disj fs -> forallb (formula_scoped depth closed) fs
| Wire_types.All f0 -> formula_scoped (Stdlib.Int.succ depth) closed f0
| Wire_types.Ex f0 -> formula_scoped (Stdlib.Int.succ depth) closed f0
| _ -> true

(** val bind_term :
    int -> int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term **)

let rec bind_term depth variable = function
| Wire_types.B i ->
  Wire_types.B (if (<=) depth i then Stdlib.Int.succ i else i)
| Wire_types.F i ->
  if (=) i variable then Wire_types.B depth else Wire_types.F i
| Wire_types.App (s, ts) ->
  Wire_types.App (s, (map (bind_term depth variable) ts))

(** val bind_formula :
    int -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula **)

let rec bind_formula depth variable = function
| Wire_types.Pred (p, ts) ->
  Wire_types.Pred (p, (map (bind_term depth variable) ts))
| Wire_types.Eq (x, y) ->
  Wire_types.Eq ((bind_term depth variable x), (bind_term depth variable y))
| Wire_types.Neg f0 -> Wire_types.Neg (bind_formula depth variable f0)
| Wire_types.Conj fs -> Wire_types.Conj (map (bind_formula depth variable) fs)
| Wire_types.Disj fs -> Wire_types.Disj (map (bind_formula depth variable) fs)
| Wire_types.All f0 ->
  Wire_types.All (bind_formula (Stdlib.Int.succ depth) variable f0)
| Wire_types.Ex f0 ->
  Wire_types.Ex (bind_formula (Stdlib.Int.succ depth) variable f0)
| x -> x

(** val lift_term :
    int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term **)

let rec lift_term depth = function
| Wire_types.B i -> Wire_types.B ((+) depth i)
| Wire_types.F i -> Wire_types.F i
| Wire_types.App (s, ts) -> Wire_types.App (s, (map (lift_term depth) ts))

(** val substitute_term :
    int -> int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term ->
    'a1 Wire_types.source_term **)

let rec substitute_term depth variable replacement = function
| Wire_types.B i -> Wire_types.B i
| Wire_types.F i ->
  if (=) i variable then lift_term depth replacement else Wire_types.F i
| Wire_types.App (s, ts) ->
  Wire_types.App (s, (map (substitute_term depth variable replacement) ts))

(** val substitute_formula :
    int -> int -> 'a1 Wire_types.source_term -> ('a1, 'a2)
    Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula **)

let rec substitute_formula depth variable replacement = function
| Wire_types.Pred (p, ts) ->
  Wire_types.Pred (p, (map (substitute_term depth variable replacement) ts))
| Wire_types.Eq (x, y) ->
  Wire_types.Eq ((substitute_term depth variable replacement x),
    (substitute_term depth variable replacement y))
| Wire_types.Neg f0 ->
  Wire_types.Neg (substitute_formula depth variable replacement f0)
| Wire_types.Conj fs ->
  Wire_types.Conj (map (substitute_formula depth variable replacement) fs)
| Wire_types.Disj fs ->
  Wire_types.Disj (map (substitute_formula depth variable replacement) fs)
| Wire_types.All f0 ->
  Wire_types.All
    (substitute_formula (Stdlib.Int.succ depth) variable replacement f0)
| Wire_types.Ex f0 ->
  Wire_types.Ex
    (substitute_formula (Stdlib.Int.succ depth) variable replacement f0)
| x -> x

type boolean_node =
| BTrue
| BFalse
| BKeep of int
| BNot of int
| BAnd of int list
| BOr of int list

module HandleOrder =
 struct
  type t = int

  (** val leb : int -> int -> bool **)

  let leb =
    (<=)
 end

module HandleSort = Sort(HandleOrder)

(** val unique_after : int -> int list -> int list **)

let rec unique_after previous = function
| [] -> []
| id :: ids0 ->
  if (=) previous id
  then unique_after previous ids0
  else id :: (unique_after id ids0)

(** val unique_sorted : int list -> int list **)

let unique_sorted = function
| [] -> []
| id :: ids0 -> id :: (unique_after id ids0)

(** val sort_handles : int list -> int list **)

let sort_handles ids =
  unique_sorted (HandleSort.sort ids)

(** val flatten_and : (int -> boolean_node) -> int list -> int list **)

let flatten_and view ids =
  flat_map (fun id ->
    match view id with
    | BTrue -> []
    | BAnd xs -> xs
    | _ -> id :: []) ids

(** val flatten_or : (int -> boolean_node) -> int list -> int list **)

let flatten_or view ids =
  flat_map (fun id ->
    match view id with
    | BFalse -> []
    | BOr xs -> xs
    | _ -> id :: []) ids

(** val is_false : (int -> boolean_node) -> int -> bool **)

let is_false view id =
  match view id with
  | BFalse -> true
  | _ -> false

(** val is_true : (int -> boolean_node) -> int -> bool **)

let is_true view id =
  match view id with
  | BTrue -> true
  | _ -> false

(** val boolean_not : (int -> boolean_node) -> int -> boolean_node **)

let boolean_not view id =
  match view id with
  | BTrue -> BFalse
  | BFalse -> BTrue
  | BNot x -> BKeep x
  | _ -> BNot id

(** val boolean_and : (int -> boolean_node) -> int list -> boolean_node **)

let boolean_and view ids =
  let ids0 = flatten_and view ids in
  if existsb (is_false view) ids0
  then BFalse
  else (match sort_handles ids0 with
        | [] -> BTrue
        | id :: l ->
          (match l with
           | [] -> BKeep id
           | n :: l0 -> BAnd (id :: (n :: l0))))

(** val boolean_or : (int -> boolean_node) -> int list -> boolean_node **)

let boolean_or view ids =
  let ids0 = flatten_or view ids in
  if existsb (is_true view) ids0
  then BTrue
  else (match sort_handles ids0 with
        | [] -> BFalse
        | id :: l ->
          (match l with
           | [] -> BKeep id
           | n :: l0 -> BOr (id :: (n :: l0))))

type schema_kind =
| Comprehension
| Separation
| Replacement
| UnrestrictedSeparation

(** val schema_arity : schema_kind -> int **)

let schema_arity = function
| Replacement -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| _ -> Stdlib.Int.succ 0

(** val term_parameters_below : int -> 'a1 Wire_types.source_term -> bool **)

let rec term_parameters_below limit = function
| Wire_types.B _ -> true
| Wire_types.F i -> negb ((<=) limit i)
| Wire_types.App (_, ts) -> forallb (term_parameters_below limit) ts

(** val parameters_below :
    int -> ('a1, 'a2) Wire_types.source_formula -> bool **)

let rec parameters_below limit = function
| Wire_types.Pred (_, ts) -> forallb (term_parameters_below limit) ts
| Wire_types.Eq (x, y) ->
  (&&) (term_parameters_below limit x) (term_parameters_below limit y)
| Wire_types.Neg f0 -> parameters_below limit f0
| Wire_types.Conj fs -> forallb (parameters_below limit) fs
| Wire_types.Disj fs -> forallb (parameters_below limit) fs
| Wire_types.All f0 -> parameters_below limit f0
| Wire_types.Ex f0 -> parameters_below limit f0
| _ -> true

(** val implication :
    ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula **)

let implication f g =
  Wire_types.Disj ((Wire_types.Neg f) :: (g :: []))

(** val equivalence :
    ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula **)

let equivalence f g =
  Wire_types.Conj ((implication f g) :: ((implication g f) :: []))

(** val all_free :
    int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula **)

let all_free variable f =
  Wire_types.All (bind_formula 0 variable f)

(** val ex_free :
    int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula **)

let ex_free variable f =
  Wire_types.Ex (bind_formula 0 variable f)

(** val close_parameters :
    int list -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula **)

let close_parameters variables f =
  fold_right all_free f variables

(** val replacement_unique :
    int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula **)

let replacement_unique fresh phi =
  let z = Wire_types.F (Stdlib.Int.succ (Stdlib.Int.succ fresh)) in
  all_free (Stdlib.Int.succ (Stdlib.Int.succ fresh))
    (implication (substitute_formula 0 (Stdlib.Int.succ 0) z phi)
      (Wire_types.Eq (z, (Wire_types.F (Stdlib.Int.succ 0)))))

(** val replacement_functional :
    int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula **)

let replacement_functional fresh phi =
  all_free 0
    (ex_free (Stdlib.Int.succ 0) (Wire_types.Conj
      (phi :: ((replacement_unique fresh phi) :: []))))

(** val replacement_image :
    'a2 -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
    Wire_types.source_formula **)

let replacement_image member fresh phi =
  all_free fresh
    (ex_free (Stdlib.Int.succ fresh)
      (all_free (Stdlib.Int.succ 0)
        (equivalence (Wire_types.Pred (member, ((Wire_types.F (Stdlib.Int.succ
          0)) :: ((Wire_types.F (Stdlib.Int.succ fresh)) :: []))))
          (ex_free 0 (Wire_types.Conj ((Wire_types.Pred (member,
            ((Wire_types.F 0) :: ((Wire_types.F
            fresh) :: [])))) :: (phi :: [])))))))

(** val schema_core :
    schema_kind -> 'a2 -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1,
    'a2) Wire_types.source_formula **)

let schema_core kind member fresh phi =
  let x = Wire_types.F 0 in
  let set = Wire_types.F fresh in
  let result = Wire_types.F (Stdlib.Int.succ fresh) in
  (match kind with
   | Separation ->
     all_free fresh
       (ex_free (Stdlib.Int.succ fresh)
         (all_free 0
           (equivalence (Wire_types.Pred (member, (x :: (result :: []))))
             (Wire_types.Conj ((Wire_types.Pred (member,
             (x :: (set :: [])))) :: (phi :: []))))))
   | Replacement ->
     implication (replacement_functional fresh phi)
       (replacement_image member fresh phi)
   | _ ->
     ex_free (Stdlib.Int.succ fresh)
       (all_free 0
         (equivalence (Wire_types.Pred (member, (x :: (result :: [])))) phi)))

(** val expand_schema :
    schema_kind -> 'a2 -> int list -> int -> ('a1, 'a2)
    Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula **)

let expand_schema kind member variables fresh phi =
  close_parameters variables (schema_core kind member fresh phi)

(** val checked_schema :
    schema_kind -> 'a2 -> int list -> int -> ('a1, 'a2)
    Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula option **)

let checked_schema kind member variables fresh phi =
  if (&&) ((&&) ((<=) (schema_arity kind) fresh) (formula_scoped 0 false phi))
       (parameters_below fresh phi)
  then let f = expand_schema kind member variables fresh phi in
       if formula_scoped 0 true f then Some f else None
  else None

type ('f, 'p) normal =
| NPred of bool * 'p * 'f Wire_types.source_term list
| NEqual of bool * 'f Wire_types.source_term * 'f Wire_types.source_term
| NConj of ('f, 'p) normal list
| NDisj of ('f, 'p) normal list
| NAll of ('f, 'p) normal
| NEx of ('f, 'p) normal

(** val nnf :
    bool -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2) normal **)

let rec nnf positive0 = function
| Wire_types.Top -> if positive0 then NConj [] else NDisj []
| Wire_types.Bot -> if positive0 then NDisj [] else NConj []
| Wire_types.Pred (p, ts) -> NPred (positive0, p, ts)
| Wire_types.Eq (x, y) -> NEqual (positive0, x, y)
| Wire_types.Neg f0 -> nnf (negb positive0) f0
| Wire_types.Conj fs ->
  if positive0
  then NConj (map (nnf positive0) fs)
  else NDisj (map (nnf positive0) fs)
| Wire_types.Disj fs ->
  if positive0
  then NDisj (map (nnf positive0) fs)
  else NConj (map (nnf positive0) fs)
| Wire_types.All f0 ->
  if positive0 then NAll (nnf true f0) else NEx (nnf false f0)
| Wire_types.Ex f0 ->
  if positive0 then NEx (nnf true f0) else NAll (nnf false f0)

(** val normal_scoped : int -> bool -> ('a1, 'a2) normal -> bool **)

let rec normal_scoped depth closed = function
| NPred (_, _, ts) -> forallb (term_scoped depth closed) ts
| NEqual (_, x, y) ->
  (&&) (term_scoped depth closed x) (term_scoped depth closed y)
| NConj fs -> forallb (normal_scoped depth closed) fs
| NDisj fs -> forallb (normal_scoped depth closed) fs
| NAll f0 -> normal_scoped (Stdlib.Int.succ depth) closed f0
| NEx f0 -> normal_scoped (Stdlib.Int.succ depth) closed f0

type 'l matrix =
| MLiteral of 'l
| MConj of 'l matrix list
| MDisj of 'l matrix list

(** val distribute : 'a1 list list -> 'a1 list list -> 'a1 list list **)

let distribute xs ys =
  flat_map (fun x -> map (app x) ys) xs

(** val product_fits : int -> int -> int -> bool **)

let rec product_fits remaining rows width =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun rows0 ->
    (&&) ((<=) width remaining)
      (product_fits ((fun n m -> Stdlib.max 0 (n-m)) remaining width) rows0
        width))
    rows

(** val bounded_distribute :
    int -> 'a1 list list -> 'a1 list list -> 'a1 list list option **)

let bounded_distribute limit xs ys =
  if product_fits limit (length xs) (length ys)
  then Some (distribute xs ys)
  else None

(** val bounded_identity : int -> 'a1 list list -> 'a1 list list option **)

let bounded_identity limit xs =
  if (<=) (length xs) limit then Some xs else None

(** val bounded_cnf :
    (unit -> bool) -> int -> 'a1 matrix -> 'a1 list list option **)

let rec bounded_cnf visit limit m =
  if visit ()
  then (match m with
        | MLiteral l -> bounded_identity limit ((l :: []) :: [])
        | MConj ms ->
          let rec join remaining = function
          | [] -> Some []
          | m0 :: ms1 ->
            (match bounded_cnf visit limit m0 with
             | Some xs ->
               if (<=) (length xs) remaining
               then (match join
                             ((fun n m -> Stdlib.max 0 (n-m)) remaining
                               (length xs))
                             ms1 with
                     | Some ys -> Some (app xs ys)
                     | None -> None)
               else None
             | None -> None)
          in join limit ms
        | MDisj ms ->
          let rec join acc = function
          | [] -> bounded_identity limit acc
          | m0 :: ms1 ->
            (match bounded_cnf visit limit m0 with
             | Some ys ->
               (match bounded_distribute limit acc ys with
                | Some xs -> join xs ms1
                | None -> None)
             | None -> None)
          in join ([] :: []) ms)
  else None

type 'a definition_literal =
| DBase of bool * 'a
| DAux of bool * int * int list

type 'a definition = { conjunction : bool; arguments : int list;
                       children : 'a definition_literal list }

(** val opposite : 'a1 definition_literal -> 'a1 definition_literal **)

let opposite = function
| DBase (b, a) -> DBase ((negb b), a)
| DAux (b, id, vs) -> DAux ((negb b), id, vs)

(** val definition_root : int -> 'a1 definition -> 'a1 definition_literal **)

let definition_root id d =
  DAux (true, id, d.arguments)

(** val definition_clauses :
    int -> 'a1 definition -> 'a1 definition_literal list list **)

let definition_clauses id d =
  let root = definition_root id d in
  if d.conjunction
  then app (map (fun child -> (opposite root) :: (child :: [])) d.children)
         ((root :: (map opposite d.children)) :: [])
  else app (((opposite root) :: d.children) :: [])
         (map (fun child -> root :: ((opposite child) :: [])) d.children)

(** val literal_variables :
    ('a1 -> int list) -> 'a1 definition_literal -> int list **)

let literal_variables support = function
| DBase (_, a) -> support a
| DAux (_, _, vs) -> vs

(** val definition_variables :
    ('a1 -> int list) -> 'a1 definition_literal list -> int list **)

let definition_variables support ls =
  sort_handles (flat_map (literal_variables support) ls)

(** val literal_before : int -> 'a1 definition_literal -> bool **)

let literal_before limit = function
| DBase (_, _) -> true
| DAux (_, id, _) -> negb ((<=) limit id)

(** val definition_valid :
    ('a1 -> int list) -> int -> 'a1 definition -> bool **)

let definition_valid support id d =
  (&&) (forallb (literal_before id) d.children)
    (forallb (fun v -> existsb ((=) v) d.arguments)
      (flat_map (literal_variables support) d.children))

(** val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forallb2 test xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs0 ->
    (match ys with
     | [] -> false
     | y :: ys0 -> (&&) (test x y) (forallb2 test xs0 ys0))

(** val valid_prefix :
    (int -> 'a1 definition option) -> ('a1 -> int list) -> int -> bool **)

let rec valid_prefix lookup support size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun size0 ->
    (&&) (valid_prefix lookup support size0)
      (match lookup size0 with
       | Some d -> definition_valid support size0 d
       | None -> false))
    size

(** val match_connective :
    (int -> 'a1 definition option) -> bool -> ('a1 definition_literal list ->
    bool) -> int -> 'a1 definition_literal -> bool **)

let match_connective lookup expected check_children size = function
| DBase (_, _) -> false
| DAux (b, id, vars) ->
  if b
  then (&&) (negb ((<=) size id))
         (match lookup id with
          | Some d ->
            (&&)
              ((&&) (eqb expected d.conjunction)
                (forallb2 (=) vars d.arguments))
              (check_children d.children)
          | None -> false)
  else false

(** val matches_matrix :
    (int -> 'a1 definition option) -> ('a1 -> 'a1 -> bool) -> int ->
    (bool * 'a1) matrix -> 'a1 definition_literal -> bool **)

let rec matches_matrix lookup equal size m root =
  match m with
  | MLiteral p ->
    let (sign, atom0) = p in
    (match root with
     | DBase (other, b) -> (&&) (eqb sign other) (equal atom0 b)
     | DAux (_, _, _) -> false)
  | MConj ms ->
    match_connective lookup true
      (forallb2 (matches_matrix lookup equal size) ms) size root
  | MDisj ms ->
    match_connective lookup false
      (forallb2 (matches_matrix lookup equal size) ms) size root

(** val emit_definitions :
    (int -> 'a1 definition option) -> (unit -> bool) -> int -> int -> int ->
    'a1 definition_literal list list option **)

let rec emit_definitions lookup visit count first budget =
  if visit ()
  then ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Some [])
          (fun count0 ->
          match lookup first with
          | Some d ->
            if negb ((<=) budget (length d.children))
            then let cs = definition_clauses first d in
                 (match emit_definitions lookup visit count0 (Stdlib.Int.succ
                          first)
                          ((fun n m -> Stdlib.max 0 (n-m)) budget (length cs)) with
                  | Some rest -> Some (app cs rest)
                  | None -> None)
            else None
          | None -> None)
          count)
  else None

(** val checked_definitions :
    (int -> 'a1 definition option) -> (unit -> bool) -> ('a1 -> 'a1 -> bool)
    -> ('a1 -> int list) -> int -> int -> (bool * 'a1) matrix -> 'a1
    definition_literal -> 'a1 definition_literal list list option **)

let checked_definitions lookup visit equal support size budget m root =
  if (&&)
       ((&&) ((&&) (visit ()) (valid_prefix lookup support size))
         (matches_matrix lookup equal size m root))
       ((<=) (Stdlib.Int.succ 0) budget)
  then (match emit_definitions lookup visit size 0
                ((fun n m -> Stdlib.max 0 (n-m)) budget (Stdlib.Int.succ 0)) with
        | Some cs -> Some (app cs ((root :: []) :: []))
        | None -> None)
  else None

(** val map_option : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec map_option f = function
| [] -> Some []
| x :: xs0 ->
  (match f x with
   | Some y ->
     (match map_option f xs0 with
      | Some ys -> Some (y :: ys)
      | None -> None)
   | None -> None)

(** val instantiate_bound :
    (unit -> bool) -> ('a1 -> 'a2 list -> 'a2) -> 'a2 list -> 'a1
    Wire_types.source_term -> 'a2 option **)

let rec instantiate_bound visit apply env t0 =
  if visit ()
  then (match t0 with
        | Wire_types.B i -> nth_error env i
        | Wire_types.F _ -> None
        | Wire_types.App (f, ts) ->
          (match map_option (instantiate_bound visit apply env) ts with
           | Some args -> Some (apply f args)
           | None -> None))
  else None

type 'l universal =
| ULiteral of 'l
| UConj of 'l universal list
| UDisj of 'l universal list
| UAll of int * 'l universal

(** val scope_list :
    (int -> 'a1 -> int option) -> int -> 'a1 list -> int option **)

let rec scope_list check next = function
| [] -> Some next
| x :: xs0 ->
  (match check next x with
   | Some after -> scope_list check after xs0
   | None -> None)

(** val erase_universals : 'a1 universal -> 'a1 matrix **)

let rec erase_universals = function
| ULiteral l -> MLiteral l
| UConj fs -> MConj (map erase_universals fs)
| UDisj fs -> MDisj (map erase_universals fs)
| UAll (_, f0) -> erase_universals f0

(** val universal_scope :
    ('a1 -> int list) -> int list -> int -> int -> 'a1 universal -> int option **)

let rec universal_scope support allowed limit next = function
| ULiteral l ->
  if forallb (fun v -> existsb ((=) v) allowed) (support l)
  then Some next
  else None
| UConj fs -> scope_list (universal_scope support allowed limit) next fs
| UDisj fs -> scope_list (universal_scope support allowed limit) next fs
| UAll (v, f0) ->
  if (&&) ((=) v next) (negb ((<=) limit next))
  then universal_scope support (v :: allowed) limit (Stdlib.Int.succ next) f0
  else None

(** val checked_universals :
    ('a1 -> int list) -> int -> 'a1 universal -> 'a1 matrix option **)

let checked_universals support limit f =
  match universal_scope support [] limit 0 f with
  | Some _ -> Some (erase_universals f)
  | None -> None

type 'x supplied = { supplied_value : 'x; next_variable : int;
                     next_symbol : int }

(** val supply : 'a1 -> int -> int -> 'a1 supplied **)

let supply value variable symbol =
  { supplied_value = value; next_variable = variable; next_symbol = symbol }

(** val map_supply :
    (int -> int -> 'a1 -> 'a2 supplied option) -> int -> int -> 'a1 list ->
    'a2 list supplied option **)

let rec map_supply compile variable symbol = function
| [] -> Some (supply [] variable symbol)
| x :: xs0 ->
  (match compile variable symbol x with
   | Some first ->
     (match map_supply compile first.next_variable first.next_symbol xs0 with
      | Some rest ->
        Some
          (supply (first.supplied_value :: rest.supplied_value)
            rest.next_variable rest.next_symbol)
      | None -> None)
   | None -> None)

(** val eliminate_quantifiers :
    (unit -> bool) -> ('a1 -> 'a3 list -> 'a3) -> (int -> 'a3) -> (int -> 'a3
    list -> 'a3) -> (bool -> 'a2 -> 'a3 list -> 'a4) -> (bool -> 'a3 -> 'a3 ->
    'a4) -> int -> 'a3 list -> 'a3 list -> int -> int -> ('a1, 'a2) normal ->
    'a4 universal supplied option **)

let rec eliminate_quantifiers visit apply variable witness predicate equality limit env universals next_v next_s f =
  if visit ()
  then (match f with
        | NPred (sign, p, ts) ->
          (match map_option (instantiate_bound visit apply env) ts with
           | Some args ->
             Some (supply (ULiteral (predicate sign p args)) next_v next_s)
           | None -> None)
        | NEqual (sign, x, y) ->
          (match instantiate_bound visit apply env x with
           | Some x0 ->
             (match instantiate_bound visit apply env y with
              | Some y0 ->
                Some (supply (ULiteral (equality sign x0 y0)) next_v next_s)
              | None -> None)
           | None -> None)
        | NConj fs ->
          (match map_supply
                   (eliminate_quantifiers visit apply variable witness
                     predicate equality limit env universals)
                   next_v next_s fs with
           | Some r ->
             Some
               (supply (UConj r.supplied_value) r.next_variable r.next_symbol)
           | None -> None)
        | NDisj fs ->
          (match map_supply
                   (eliminate_quantifiers visit apply variable witness
                     predicate equality limit env universals)
                   next_v next_s fs with
           | Some r ->
             Some
               (supply (UDisj r.supplied_value) r.next_variable r.next_symbol)
           | None -> None)
        | NAll f0 ->
          if negb ((<=) limit next_v)
          then let term0 = variable next_v in
               (match eliminate_quantifiers visit apply variable witness
                        predicate equality limit (term0 :: env)
                        (app universals (term0 :: [])) (Stdlib.Int.succ
                        next_v) next_s f0 with
                | Some r ->
                  Some
                    (supply (UAll (next_v, r.supplied_value)) r.next_variable
                      r.next_symbol)
                | None -> None)
          else None
        | NEx f0 ->
          if negb ((<=) limit next_s)
          then eliminate_quantifiers visit apply variable witness predicate
                 equality limit ((witness next_s universals) :: env)
                 universals next_v (Stdlib.Int.succ next_s) f0
          else None)
  else None

type 'f wire_symbol =
| Original of 'f
| Skolem of int * int

type 'pT wire_predicate =
| Named of 'pT
| Auxiliary of (int * int)

type 'f wire_term =
| V of (int * int)
| Fn of 'f wire_symbol * 'f wire_term list

type ('f, 'pT) wire_atom =
| P of 'pT * 'f wire_term list
| E of 'f wire_term * 'f wire_term
| D of (int * int) * 'f wire_term list

type ('f, 'pT) wire_literal = { positive : bool; atom : ('f, 'pT) wire_atom }

(** val term_indices_acc : 'a1 wire_term -> int list -> int list **)

let rec term_indices_acc t0 acc =
  match t0 with
  | V p -> let (_, i) = p in i :: acc
  | Fn (_, ts) -> fold_left (fun acc0 t1 -> term_indices_acc t1 acc0) ts acc

(** val atom_indices_acc : ('a1, 'a2) wire_atom -> int list **)

let atom_indices_acc = function
| P (_, ts) -> fold_left (fun acc t0 -> term_indices_acc t0 acc) ts []
| E (x, y) -> term_indices_acc y (term_indices_acc x [])
| D (_, ts) -> fold_left (fun acc t0 -> term_indices_acc t0 acc) ts []

(** val wire_support : ('a1, 'a2) wire_atom -> int list **)

let wire_support a =
  sort_handles (atom_indices_acc a)

(** val local_variable : (int * int) -> bool **)

let local_variable v =
  (&&) ((=) (fst v) 0) ((<=) 0 (snd v))

(** val wire_term_local : 'a1 wire_term -> bool **)

let rec wire_term_local = function
| V v -> local_variable v
| Fn (_, ts) -> forallb wire_term_local ts

(** val wire_base_valid : ('a1, 'a2) wire_atom -> bool **)

let wire_base_valid = function
| P (_, ts) -> forallb wire_term_local ts
| E (x, y) -> (&&) (wire_term_local x) (wire_term_local y)
| D (_, _) -> false

(** val checked_wire_support : ('a1, 'a2) wire_atom -> int list option **)

let checked_wire_support a =
  if wire_base_valid a then Some (wire_support a) else None

(** val wire_quantifiers :
    (unit -> bool) -> int -> int -> ('a1, 'a2) normal -> (bool * ('a1, 'a2)
    wire_atom) universal supplied option **)

let wire_quantifiers visit limit ax normal0 =
  eliminate_quantifiers visit (fun f ts -> Fn ((Original f), ts)) (fun i -> V
    (0, i)) (fun id ts -> Fn ((Skolem (ax, id)), ts)) (fun sign p ts -> (sign,
    (P (p, ts)))) (fun sign x y -> (sign, (E (x, y)))) limit [] [] 0 0 normal0

(** val wire_universal_scope :
    (unit -> bool) -> int list -> int -> int -> (bool * ('a1, 'a2) wire_atom)
    universal -> int option **)

let rec wire_universal_scope visit allowed limit next = function
| ULiteral l ->
  if visit ()
  then (match checked_wire_support (snd l) with
        | Some vars ->
          if forallb (fun v -> existsb ((=) v) allowed) vars
          then Some next
          else None
        | None -> None)
  else None
| UConj fs -> scope_list (wire_universal_scope visit allowed limit) next fs
| UDisj fs -> scope_list (wire_universal_scope visit allowed limit) next fs
| UAll (v, body) ->
  if (&&) ((=) v next) (negb ((<=) limit next))
  then wire_universal_scope visit (v :: allowed) limit (Stdlib.Int.succ next)
         body
  else None

(** val wire_checked_universals :
    (unit -> bool) -> int -> (bool * ('a1, 'a2) wire_atom) universal ->
    (bool * ('a1, 'a2) wire_atom) matrix option **)

let wire_checked_universals visit limit f =
  match wire_universal_scope visit [] limit 0 f with
  | Some _ -> Some (erase_universals f)
  | None -> None

(** val pack_literal :
    (bool * ('a1, 'a2) wire_atom) -> ('a1, 'a2) wire_literal **)

let pack_literal l =
  { positive = (fst l); atom = (snd l) }

(** val wire_distributive_cnf :
    (unit -> bool) -> int -> (bool * ('a1, 'a2) wire_atom) matrix -> ('a1,
    'a2) wire_literal list list option **)

let wire_distributive_cnf visit budget m =
  match bounded_cnf visit budget m with
  | Some cs -> Some (map (map pack_literal) cs)
  | None -> None

(** val wire_definition_valid :
    ('a1, 'a2) wire_atom definition_literal -> bool **)

let wire_definition_valid = function
| DBase (_, a) -> wire_base_valid a
| DAux (_, id, vars) -> (&&) ((<=) 0 id) (forallb (fun v -> (<=) 0 v) vars)

(** val wire_lookup :
    (int -> ('a1, 'a2) wire_atom definition option) -> int -> ('a1, 'a2)
    wire_atom definition option **)

let wire_lookup lookup id =
  match lookup id with
  | Some d ->
    if forallb wire_definition_valid d.children then Some d else None
  | None -> None

(** val wire_definitions_valid :
    (int -> ('a1, 'a2) wire_atom definition option) -> int -> bool **)

let rec wire_definitions_valid lookup size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun size0 ->
    if wire_definitions_valid lookup size0
    then (match wire_lookup lookup size0 with
          | Some _ -> true
          | None -> false)
    else false)
    size

(** val pack_definition :
    int -> ('a1, 'a2) wire_atom definition_literal -> ('a1, 'a2) wire_literal **)

let pack_definition ax = function
| DBase (sign, a) -> { positive = sign; atom = a }
| DAux (sign, id, vars) ->
  { positive = sign; atom = (D ((ax, id), (map (fun i -> V (0, i)) vars))) }

(** val wire_definitional_cnf :
    (int -> ('a1, 'a2) wire_atom definition option) -> (unit -> bool) ->
    (('a1, 'a2) wire_atom -> ('a1, 'a2) wire_atom -> bool) -> int -> int ->
    int -> (bool * ('a1, 'a2) wire_atom) matrix -> ('a1, 'a2) wire_atom
    definition_literal -> ('a1, 'a2) wire_literal list list option **)

let wire_definitional_cnf lookup visit equal size budget ax m root =
  if (&&) ((&&) (visit ()) (wire_definition_valid root))
       (wire_definitions_valid lookup size)
  then (match checked_definitions lookup visit equal wire_support size budget
                m root with
        | Some cs -> Some (map (map (pack_definition ax)) cs)
        | None -> None)
  else None

type formula = (string, string) Wire_types.source_formula

type term = string Wire_types.source_term

(** val term_equal : term -> term -> bool **)

let rec term_equal a b =
  match a with
  | Wire_types.B i -> (match b with
                       | Wire_types.B j -> (=) i j
                       | _ -> false)
  | Wire_types.F i -> (match b with
                       | Wire_types.F j -> (=) i j
                       | _ -> false)
  | Wire_types.App (f, xs) ->
    (match b with
     | Wire_types.App (g, ys) -> (&&) ((=) f g) (forallb2 term_equal xs ys)
     | _ -> false)

(** val formula_equal : formula -> formula -> bool **)

let rec formula_equal a b =
  match a with
  | Wire_types.Top -> (match b with
                       | Wire_types.Top -> true
                       | _ -> false)
  | Wire_types.Bot -> (match b with
                       | Wire_types.Bot -> true
                       | _ -> false)
  | Wire_types.Pred (p, xs) ->
    (match b with
     | Wire_types.Pred (q, ys) -> (&&) ((=) p q) (forallb2 term_equal xs ys)
     | _ -> false)
  | Wire_types.Eq (x, y) ->
    (match b with
     | Wire_types.Eq (u, v) -> (&&) (term_equal x u) (term_equal y v)
     | _ -> false)
  | Wire_types.Neg f ->
    (match b with
     | Wire_types.Neg g -> formula_equal f g
     | _ -> false)
  | Wire_types.Conj fs ->
    (match b with
     | Wire_types.Conj gs ->
       (&&) (forallb (fun f -> existsb (formula_equal f) gs) fs)
         (forallb (fun g -> existsb (fun f -> formula_equal f g) fs) gs)
     | _ -> false)
  | Wire_types.Disj fs ->
    (match b with
     | Wire_types.Disj gs ->
       (&&) (forallb (fun f -> existsb (formula_equal f) gs) fs)
         (forallb (fun g -> existsb (fun f -> formula_equal f g) fs) gs)
     | _ -> false)
  | Wire_types.All f ->
    (match b with
     | Wire_types.All g -> formula_equal f g
     | _ -> false)
  | Wire_types.Ex f ->
    (match b with
     | Wire_types.Ex g -> formula_equal f g
     | _ -> false)

(** val deduplicate : formula list -> formula list **)

let rec deduplicate = function
| [] -> []
| f :: fs0 ->
  if existsb (formula_equal f) fs0
  then deduplicate fs0
  else f :: (deduplicate fs0)

(** val and_parts : formula -> formula list **)

let and_parts f = match f with
| Wire_types.Top -> []
| Wire_types.Conj fs -> fs
| _ -> f :: []

(** val or_parts : formula -> formula list **)

let or_parts f = match f with
| Wire_types.Bot -> []
| Wire_types.Disj fs -> fs
| _ -> f :: []

(** val is_bottom : formula -> bool **)

let is_bottom = function
| Wire_types.Bot -> true
| _ -> false

(** val is_top : formula -> bool **)

let is_top = function
| Wire_types.Top -> true
| _ -> false

(** val smart_and :
    formula list -> (string, string) Wire_types.source_formula **)

let smart_and fs =
  let fs0 = deduplicate (flat_map and_parts fs) in
  if existsb is_bottom fs0
  then Wire_types.Bot
  else (match fs0 with
        | [] -> Wire_types.Top
        | f :: l -> (match l with
                     | [] -> f
                     | _ :: _ -> Wire_types.Conj fs0))

(** val smart_or :
    formula list -> (string, string) Wire_types.source_formula **)

let smart_or fs =
  let fs0 = deduplicate (flat_map or_parts fs) in
  if existsb is_top fs0
  then Wire_types.Top
  else (match fs0 with
        | [] -> Wire_types.Bot
        | f :: l -> (match l with
                     | [] -> f
                     | _ :: _ -> Wire_types.Disj fs0))

(** val smart_not : formula -> (string, string) Wire_types.source_formula **)

let smart_not f = match f with
| Wire_types.Top -> Wire_types.Bot
| Wire_types.Bot -> Wire_types.Top
| Wire_types.Neg g -> g
| _ -> Wire_types.Neg f

(** val simplify : formula -> formula **)

let rec simplify f = match f with
| Wire_types.Neg f0 -> smart_not (simplify f0)
| Wire_types.Conj fs -> smart_and (map simplify fs)
| Wire_types.Disj fs -> smart_or (map simplify fs)
| Wire_types.All f0 -> Wire_types.All (simplify f0)
| Wire_types.Ex f0 -> Wire_types.Ex (simplify f0)
| _ -> f

(** val formula_identical : formula -> formula -> bool **)

let rec formula_identical a b =
  match a with
  | Wire_types.Top -> (match b with
                       | Wire_types.Top -> true
                       | _ -> false)
  | Wire_types.Bot -> (match b with
                       | Wire_types.Bot -> true
                       | _ -> false)
  | Wire_types.Pred (p, xs) ->
    (match b with
     | Wire_types.Pred (q, ys) -> (&&) ((=) p q) (forallb2 term_equal xs ys)
     | _ -> false)
  | Wire_types.Eq (x, y) ->
    (match b with
     | Wire_types.Eq (u, v) -> (&&) (term_equal x u) (term_equal y v)
     | _ -> false)
  | Wire_types.Neg f ->
    (match b with
     | Wire_types.Neg g -> formula_identical f g
     | _ -> false)
  | Wire_types.Conj fs ->
    (match b with
     | Wire_types.Conj gs -> forallb2 formula_identical fs gs
     | _ -> false)
  | Wire_types.Disj fs ->
    (match b with
     | Wire_types.Disj gs -> forallb2 formula_identical fs gs
     | _ -> false)
  | Wire_types.All f ->
    (match b with
     | Wire_types.All g -> formula_identical f g
     | _ -> false)
  | Wire_types.Ex f ->
    (match b with
     | Wire_types.Ex g -> formula_identical f g
     | _ -> false)

(** val equivalent : formula -> formula -> bool **)

let equivalent a b =
  if formula_identical a b
  then true
  else formula_equal (simplify a) (simplify b)

(** val symbol_present : (string * int) list -> string -> int -> bool **)

let symbol_present symbols name arity =
  existsb (fun entry -> (&&) ((=) name (fst entry)) ((=) arity (snd entry)))
    symbols

(** val term_signature : (string * int) list -> term -> bool **)

let rec term_signature symbols = function
| Wire_types.B i -> (<=) 0 i
| Wire_types.F i -> (<=) 0 i
| Wire_types.App (f, ts) ->
  (&&) (symbol_present symbols f (length ts))
    (forallb (term_signature symbols) ts)

(** val formula_signature :
    (string * int) list -> (string * int) list -> formula -> bool **)

let rec formula_signature functions predicates = function
| Wire_types.Pred (p, ts) ->
  (&&) (symbol_present predicates p (length ts))
    (forallb (term_signature functions) ts)
| Wire_types.Eq (x, y) ->
  (&&) (term_signature functions x) (term_signature functions y)
| Wire_types.Neg f0 -> formula_signature functions predicates f0
| Wire_types.Conj fs -> forallb (formula_signature functions predicates) fs
| Wire_types.Disj fs -> forallb (formula_signature functions predicates) fs
| Wire_types.All f0 -> formula_signature functions predicates f0
| Wire_types.Ex f0 -> formula_signature functions predicates f0
| _ -> true

(** val term_parameters : term -> int list **)

let rec term_parameters = function
| Wire_types.B _ -> []
| Wire_types.F i -> i :: []
| Wire_types.App (_, ts) -> flat_map term_parameters ts

(** val formula_parameters : formula -> int list **)

let rec formula_parameters = function
| Wire_types.Pred (_, ts) -> flat_map term_parameters ts
| Wire_types.Eq (x, y) -> app (term_parameters x) (term_parameters y)
| Wire_types.Neg f0 -> formula_parameters f0
| Wire_types.Conj fs -> flat_map formula_parameters fs
| Wire_types.Disj fs -> flat_map formula_parameters fs
| Wire_types.All f0 -> formula_parameters f0
| Wire_types.Ex f0 -> formula_parameters f0
| _ -> []

(** val builtin : Wire_types.schema -> schema_kind option **)

let builtin = function
| Wire_types.Comprehension -> Some Comprehension
| Wire_types.Separation -> Some Separation
| Wire_types.Replacement -> Some Replacement
| Wire_types.Unrestricted_separation -> Some UnrestrictedSeparation
| Wire_types.Registered (_, _) -> None

(** val schema_equal : Wire_types.schema -> Wire_types.schema -> bool **)

let schema_equal x y =
  match x with
  | Wire_types.Comprehension ->
    (match y with
     | Wire_types.Comprehension -> true
     | _ -> false)
  | Wire_types.Separation ->
    (match y with
     | Wire_types.Separation -> true
     | _ -> false)
  | Wire_types.Replacement ->
    (match y with
     | Wire_types.Replacement -> true
     | _ -> false)
  | Wire_types.Unrestricted_separation ->
    (match y with
     | Wire_types.Unrestricted_separation -> true
     | _ -> false)
  | Wire_types.Registered (n, r) ->
    (match y with
     | Wire_types.Registered (m, s) -> (&&) ((=) n m) ((=) r s)
     | _ -> false)

(** val admitted : Wire_types.schema list -> Wire_types.schema -> bool **)

let admitted schemas kind =
  existsb (schema_equal kind) schemas

type theory = { theory_name : string; unrestricted_signature : bool;
                function_symbols : (string * int) list;
                predicate_symbols : (string * int) list;
                fixed_axioms : Wire_types.axiom list;
                allowed_schemas : Wire_types.schema list;
                registered_check : (string -> string -> string -> formula ->
                                   bool) }

(** val signature_ok : theory -> formula -> bool **)

let signature_ok t0 f =
  (||) t0.unrestricted_signature
    (formula_signature t0.function_symbols t0.predicate_symbols f)

(** val fixed_origin_equal :
    Wire_types.origin -> Wire_types.origin -> bool **)

let fixed_origin_equal a b =
  match a with
  | Wire_types.Fixed n ->
    (match b with
     | Wire_types.Fixed m -> (=) n m
     | _ -> false)
  | Wire_types.Imported n ->
    (match b with
     | Wire_types.Imported m -> (=) n m
     | _ -> false)
  | _ -> false

(** val schema_expansion :
    int -> schema_kind -> formula -> (string, string)
    Wire_types.source_formula option **)

let schema_expansion limit kind phi =
  let variables =
    filter (fun i -> (<=) (schema_arity kind) i)
      (sort_handles (formula_parameters phi))
  in
  let maximum =
    fold_left Nat.max variables
      ((fun n m -> Stdlib.max 0 (n-m)) (schema_arity kind) (Stdlib.Int.succ
        0))
  in
  if (<=) maximum
       ((fun n m -> Stdlib.max 0 (n-m)) limit
         (match kind with
          | Replacement ->
            Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
          | _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)))
  then checked_schema kind "member" variables (Stdlib.Int.succ maximum) phi
  else None

(** val validate_axiom : int -> theory -> Wire_types.axiom -> bool **)

let validate_axiom limit t0 a =
  (&&)
    ((&&)
      ((&&) ((<=) 0 ((fun a -> a.Wire_types.axiom_id) a))
        (formula_scoped 0 true ((fun a -> a.Wire_types.formula) a)))
      (signature_ok t0 ((fun a -> a.Wire_types.formula) a)))
    (match (fun a -> a.Wire_types.origin) a with
     | Wire_types.Fixed n ->
       (&&) ((=) ((fun a -> a.Wire_types.name) a) n)
         (existsb (fun expected ->
           (&&)
             ((&&)
               (fixed_origin_equal ((fun a -> a.Wire_types.origin) a)
                 ((fun a -> a.Wire_types.origin) expected))
               ((=) n ((fun a -> a.Wire_types.name) expected)))
             (equivalent ((fun a -> a.Wire_types.formula) expected)
               ((fun a -> a.Wire_types.formula) a)))
           t0.fixed_axioms)
     | Wire_types.Imported n ->
       (&&) ((=) ((fun a -> a.Wire_types.name) a) n)
         (existsb (fun expected ->
           (&&)
             ((&&)
               (fixed_origin_equal ((fun a -> a.Wire_types.origin) a)
                 ((fun a -> a.Wire_types.origin) expected))
               ((=) n ((fun a -> a.Wire_types.name) expected)))
             (equivalent ((fun a -> a.Wire_types.formula) expected)
               ((fun a -> a.Wire_types.formula) a)))
           t0.fixed_axioms)
     | Wire_types.Instance (key, phi) ->
       (&&)
         ((&&)
           ((&&) (admitted t0.allowed_schemas key)
             (formula_scoped 0 false phi))
           (signature_ok t0 phi))
         (match builtin key with
          | Some kind ->
            (match schema_expansion limit kind phi with
             | Some expected ->
               equivalent expected ((fun a -> a.Wire_types.formula) a)
             | None -> false)
          | None -> false)
     | Wire_types.Registered_instance (n, r, data) ->
       (&&) (admitted t0.allowed_schemas (Wire_types.Registered (n, r)))
         (t0.registered_check n r data ((fun a -> a.Wire_types.formula) a)))
