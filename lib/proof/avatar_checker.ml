
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

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

type comparison =
| Eq
| Lt
| Gt

(** val eqb : int -> int -> bool **)

let rec eqb n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      m)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun m' -> eqb n' m')
      m)
    n

(** val eqb0 : bool -> bool -> bool **)

let eqb0 b1 b2 =
  if b1 then b2 else if b2 then false else true

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p
 end

module Coq_Pos =
 struct
  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec p x0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        (fun _ -> false)
        x0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun p1 -> eq_dec p0 p1)
        (fun _ -> false)
        x0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        x0)
      p
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n0 l0))
    n

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n0 l0)
    n

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| a0 :: l0 -> let s = h a0 a in if s then true else in_dec h a l0

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

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | a :: l0 ->
    (match l' with
     | [] -> false
     | a0 :: l1 -> if eq_dec0 a a0 then list_eq_dec eq_dec0 l0 l1 else false)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: l0 -> app (f x) (flat_map f l0)

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

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup decA = function
| [] -> []
| x :: xs -> if in_dec decA x xs then nodup decA xs else x :: (nodup decA xs)

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val max : int -> int -> int **)

  let max = Stdlib.max

  (** val eq_dec : int -> int -> bool **)

  let eq_dec x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec p p0)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun p0 -> Coq_Pos.eq_dec p p0)
        y)
      x
 end

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = int

  (** val _0 : int **)

  let _0 =
    0

  (** val _1 : int **)

  let _1 =
    1

  (** val _2 : int **)

  let _2 =
    ((fun p->2*p) 1)

  (** val _3 : int **)

  let _3 =
    ((fun p->1+2*p) 1)

  (** val add : int -> int -> int **)

  let add =
    Z.add

  (** val opp : int -> int **)

  let opp =
    Z.opp

  (** val sub : int -> int -> int **)

  let sub =
    Z.sub

  (** val mul : int -> int -> int **)

  let mul =
    Z.mul

  (** val max : int -> int -> int **)

  let max =
    Z.max

  (** val eqb : int -> int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : int -> int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : int -> int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : int -> int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : int -> int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> int **)

  let i2z n =
    n
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect leaf node = function
  | Leaf -> leaf
  | Node (t1, k, e, t2, t3) ->
    node t1 (tree_rect leaf node t1) k e t2 (tree_rect leaf node t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec leaf node = function
  | Leaf -> leaf
  | Node (t1, k, e, t2, t3) ->
    node t1 (tree_rec leaf node t1) k e t2 (tree_rec leaf node t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> int **)

  let rec cardinal = function
  | Leaf -> 0
  | Node (l, _, _, r, _) -> Stdlib.Int.succ ((+) (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect end0 more = function
  | End -> end0
  | More (k, e0, t0, e1) -> more k e0 t0 e1 (enumeration_rect end0 more e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec end0 more = function
  | End -> end0
  | More (k, e0, t0, e1) -> more k e0 t0 e1 (enumeration_rec end0 more e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) -> (x, e0) :: (app (elements t0) (flatten_e r))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    Raw.add

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove =
    Raw.remove

  (** val mem : key -> 'a1 t -> bool **)

  let mem =
    Raw.mem

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find =
    Raw.find

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    Raw.map

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi =
    Raw.mapi

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 =
    Raw.map2

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements =
    Raw.elements

  (** val cardinal : 'a1 t -> int **)

  let cardinal =
    Raw.cardinal

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold =
    Raw.fold

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal =
    Raw.equal
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module Nat_as_OT =
 struct
  type t = int

  (** val compare : int -> int -> int compare0 **)

  let compare x y =
    match Nat.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    (=)
 end

(** val term_eq_dec : Rocq_checker.term -> Rocq_checker.term -> bool **)

let rec term_eq_dec x y =
  match x with
  | Rocq_checker.Var n ->
    (match y with
     | Rocq_checker.Var n0 -> (=) n n0
     | Rocq_checker.Fun (_, _) -> false)
  | Rocq_checker.Fun (n, l) ->
    (match y with
     | Rocq_checker.Var _ -> false
     | Rocq_checker.Fun (n0, l0) ->
       if (=) n n0 then list_eq_dec term_eq_dec l l0 else false)

(** val atom_eq_dec : Rocq_checker.atom -> Rocq_checker.atom -> bool **)

let atom_eq_dec x y =
  match x with
  | Rocq_checker.Pred (n, l) ->
    (match y with
     | Rocq_checker.Pred (n0, l0) ->
       if (=) n n0 then list_eq_dec term_eq_dec l l0 else false
     | Rocq_checker.Eq0 (_, _) -> false)
  | Rocq_checker.Eq0 (t0, t1) ->
    (match y with
     | Rocq_checker.Pred (_, _) -> false
     | Rocq_checker.Eq0 (t2, t3) ->
       if term_eq_dec t0 t2 then term_eq_dec t1 t3 else false)

type literal = bool * Rocq_checker.atom

type clause = literal list

(** val term_eqb : Rocq_checker.term -> Rocq_checker.term -> bool **)

let term_eqb x y =
  if term_eq_dec x y then true else false

(** val atom_eqb : Rocq_checker.atom -> Rocq_checker.atom -> bool **)

let atom_eqb x y =
  if atom_eq_dec x y then true else false

(** val atom_equiv : Rocq_checker.atom -> Rocq_checker.atom -> bool **)

let atom_equiv x y =
  (||) (atom_eqb x y)
    (match x with
     | Rocq_checker.Pred (_, _) -> false
     | Rocq_checker.Eq0 (s, t0) ->
       (match y with
        | Rocq_checker.Pred (_, _) -> false
        | Rocq_checker.Eq0 (u, v) -> (&&) (term_eqb s v) (term_eqb t0 u)))

(** val literal_equiv : literal -> literal -> bool **)

let literal_equiv x y =
  (&&) (eqb0 (fst x) (fst y)) (atom_equiv (snd x) (snd y))

(** val included : clause -> clause -> bool **)

let included xs ys =
  forallb (fun x -> existsb (literal_equiv x) ys) xs

(** val remove_at : int -> 'a1 list -> 'a1 list **)

let rec remove_at n xs =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match xs with
              | [] -> []
              | _ :: rest -> rest)
    (fun n0 ->
    match xs with
    | [] -> []
    | x :: rest -> x :: (remove_at n0 rest))
    n

(** val replace_at : int -> 'a1 -> 'a1 list -> 'a1 list **)

let replace_at n x xs =
  app (firstn n xs) (x :: (skipn (Stdlib.Int.succ n) xs))

type substitution = (int * Rocq_checker.term) list

(** val lookup : substitution -> int -> Rocq_checker.term **)

let rec lookup s v =
  match s with
  | [] -> Rocq_checker.Var v
  | p :: rest -> let (w, t0) = p in if eqb v w then t0 else lookup rest v

(** val subst_term :
    substitution -> Rocq_checker.term -> Rocq_checker.term **)

let rec subst_term s = function
| Rocq_checker.Var v -> lookup s v
| Rocq_checker.Fun (f, ts) -> Rocq_checker.Fun (f, (map (subst_term s) ts))

(** val subst_atom :
    substitution -> Rocq_checker.atom -> Rocq_checker.atom **)

let subst_atom s = function
| Rocq_checker.Pred (p, ts) -> Rocq_checker.Pred (p, (map (subst_term s) ts))
| Rocq_checker.Eq0 (x, y) ->
  Rocq_checker.Eq0 ((subst_term s x), (subst_term s y))

(** val subst_literal : substitution -> literal -> literal **)

let subst_literal s l =
  ((fst l), (subst_atom s (snd l)))

(** val subst_clause : substitution -> literal list -> literal list **)

let subst_clause s c =
  map (subst_literal s) c

(** val fill_term :
    Rocq_checker.term_context -> Rocq_checker.term -> Rocq_checker.term **)

let rec fill_term c t0 =
  match c with
  | Rocq_checker.Hole -> t0
  | Rocq_checker.Under (f, before, c0, after) ->
    Rocq_checker.Fun (f, (app before ((fill_term c0 t0) :: after)))

(** val fill_atom :
    Rocq_checker.atom_context -> Rocq_checker.term -> Rocq_checker.atom **)

let fill_atom c t0 =
  match c with
  | Rocq_checker.In_pred (p, before, ctx, after) ->
    Rocq_checker.Pred (p, (app before ((fill_term ctx t0) :: after)))
  | Rocq_checker.In_eq_left (ctx, rhs) ->
    Rocq_checker.Eq0 ((fill_term ctx t0), rhs)
  | Rocq_checker.In_eq_right (lhs, ctx) ->
    Rocq_checker.Eq0 (lhs, (fill_term ctx t0))

type literal_context = bool * Rocq_checker.atom_context

(** val fill_literal : literal_context -> Rocq_checker.term -> literal **)

let fill_literal c t0 =
  ((fst c), (fill_atom (snd c) t0))

module ClauseMap = Make(Nat_as_OT)

(** val substitution_index : substitution -> Rocq_checker.term ClauseMap.t **)

let rec substitution_index = function
| [] -> ClauseMap.empty
| p :: rest -> let (w, t0) = p in ClauseMap.add w t0 (substitution_index rest)

(** val indexed_lookup :
    Rocq_checker.term ClauseMap.t -> ClauseMap.key -> Rocq_checker.term **)

let indexed_lookup index v =
  match ClauseMap.find v index with
  | Some t0 -> t0
  | None -> Rocq_checker.Var v

(** val subst_term_with :
    (int -> Rocq_checker.term) -> Rocq_checker.term -> Rocq_checker.term **)

let rec subst_term_with look = function
| Rocq_checker.Var v -> look v
| Rocq_checker.Fun (f, ts) ->
  Rocq_checker.Fun (f, (map (subst_term_with look) ts))

(** val subst_atom_with :
    (int -> Rocq_checker.term) -> Rocq_checker.atom -> Rocq_checker.atom **)

let subst_atom_with look = function
| Rocq_checker.Pred (p, ts) ->
  Rocq_checker.Pred (p, (map (subst_term_with look) ts))
| Rocq_checker.Eq0 (x, y) ->
  Rocq_checker.Eq0 ((subst_term_with look x), (subst_term_with look y))

(** val fast_subst_clause : substitution -> clause -> clause **)

let fast_subst_clause s c =
  if (<=) (length s) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))
  then subst_clause s c
  else let index = substitution_index s in
       map (fun l -> ((fst l),
         (subst_atom_with (indexed_lookup index) (snd l)))) c

(** val infer_with :
    (int -> clause option) -> (int -> clause option) -> Rocq_checker.rule ->
    clause option **)

let infer_with input parent = function
| Rocq_checker.Input i -> input i
| Rocq_checker.Instance (p, s) ->
  (match parent p with
   | Some c -> Some (fast_subst_clause s c)
   | None -> None)
| Rocq_checker.Copy p -> parent p
| Rocq_checker.Resolve (p, i, q, j) ->
  (match parent p with
   | Some xs ->
     (match parent q with
      | Some ys ->
        (match nth_error xs i with
         | Some l ->
           (match nth_error ys j with
            | Some r0 ->
              if (&&) (negb (eqb0 (fst l) (fst r0)))
                   (atom_equiv (snd l) (snd r0))
              then Some (app (remove_at i xs) (remove_at j ys))
              else None
            | None -> None)
         | None -> None)
      | None -> None)
   | None -> None)
| Rocq_checker.Equality_resolve (p, i) ->
  (match parent p with
   | Some xs ->
     (match nth_error xs i with
      | Some l ->
        let (b, a) = l in
        if b
        then None
        else (match a with
              | Rocq_checker.Pred (_, _) -> None
              | Rocq_checker.Eq0 (x, y) ->
                if term_eqb x y then Some (remove_at i xs) else None)
      | None -> None)
   | None -> None)
| Rocq_checker.Paramodulate (p, i, reverse, q, j, context) ->
  (match parent p with
   | Some xs ->
     (match parent q with
      | Some ys ->
        (match nth_error xs i with
         | Some l ->
           let (b, a) = l in
           if b
           then (match a with
                 | Rocq_checker.Pred (_, _) -> None
                 | Rocq_checker.Eq0 (x, y) ->
                   (match nth_error ys j with
                    | Some target ->
                      let lhs = if reverse then y else x in
                      let rhs = if reverse then x else y in
                      if literal_equiv target (fill_literal context lhs)
                      then Some
                             (app (remove_at i xs)
                               (replace_at j (fill_literal context rhs) ys))
                      else None
                    | None -> None))
           else None
         | None -> None)
      | None -> None)
   | None -> None)
| Rocq_checker.Equality_factor (p, i, reverse_i, j, reverse_j) ->
  (match parent p with
   | Some xs ->
     (match nth_error xs i with
      | Some l ->
        let (b, a) = l in
        if b
        then (match a with
              | Rocq_checker.Pred (_, _) -> None
              | Rocq_checker.Eq0 (s, t0) ->
                (match nth_error xs j with
                 | Some l0 ->
                   let (b0, a0) = l0 in
                   if b0
                   then (match a0 with
                         | Rocq_checker.Pred (_, _) -> None
                         | Rocq_checker.Eq0 (u, v) ->
                           let lhs = if reverse_i then t0 else s in
                           let rhs = if reverse_i then s else t0 in
                           let lhs' = if reverse_j then v else u in
                           let rhs' = if reverse_j then u else v in
                           if term_eqb lhs lhs'
                           then Some ((false, (Rocq_checker.Eq0 (rhs,
                                  rhs'))) :: ((true, (Rocq_checker.Eq0 (u,
                                  v))) :: (remove_at i xs)))
                           else None)
                   else None
                 | None -> None))
        else None
      | None -> None)
   | None -> None)

(** val index_from : 'a1 list -> ClauseMap.key -> 'a1 ClauseMap.t **)

let rec index_from xs offset =
  match xs with
  | [] -> ClauseMap.empty
  | x :: xs0 ->
    ClauseMap.add offset x (index_from xs0 (Stdlib.Int.succ offset))

(** val cached : 'a1 list -> int -> 'a1 option **)

let cached xs =
  let table = index_from xs 0 in (fun i -> ClauseMap.find i table)

(** val term_variables : Rocq_checker.term -> int list **)

let rec term_variables = function
| Rocq_checker.Var v -> v :: []
| Rocq_checker.Fun (_, ts) -> flat_map term_variables ts

(** val atom_variables : Rocq_checker.atom -> int list **)

let atom_variables = function
| Rocq_checker.Pred (_, ts) -> flat_map term_variables ts
| Rocq_checker.Eq0 (x, y) -> app (term_variables x) (term_variables y)

(** val literal_variables : literal -> int list **)

let literal_variables l =
  atom_variables (snd l)

(** val clause_variables : clause -> int list **)

let clause_variables c =
  flat_map literal_variables c

(** val vars_disjoint : clause -> clause -> bool **)

let vars_disjoint a b =
  forallb (fun v -> negb (existsb ((=) v) (clause_variables b)))
    (clause_variables a)

(** val components_disjoint : clause list -> bool **)

let rec components_disjoint = function
| [] -> true
| c :: cs0 -> (&&) (forallb (vars_disjoint c) cs0) (components_disjoint cs0)

type fo_rule =
| Ordinary of Rocq_checker.rule
| Component of int

type fo_step = fo_rule * clause

type annotated = clause * int list

(** val rule_parents : Rocq_checker.rule -> int list **)

let rule_parents = function
| Rocq_checker.Input _ -> []
| Rocq_checker.Instance (p, _) -> p :: []
| Rocq_checker.Copy p -> p :: []
| Rocq_checker.Resolve (p, _, q, _) -> p :: (q :: [])
| Rocq_checker.Equality_resolve (p, _) -> p :: []
| Rocq_checker.Paramodulate (p, _, _, q, _, _) -> p :: (q :: [])
| Rocq_checker.Equality_factor (p, _, _, _, _) -> p :: []

(** val nodup_indexed : int list -> int list * unit ClauseMap.t **)

let rec nodup_indexed = function
| [] -> ([], ClauseMap.empty)
| x :: rest ->
  let (kept, seen) = nodup_indexed rest in
  if ClauseMap.mem x seen
  then (kept, seen)
  else ((x :: kept), (ClauseMap.add x () seen))

(** val fast_nodup : int list -> int list **)

let fast_nodup xs =
  if (<=) (length xs) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ
       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  then nodup (=) xs
  else fst (nodup_indexed xs)

(** val gather_dependencies_with :
    (int -> annotated option) -> int list -> int list option **)

let rec gather_dependencies_with parent = function
| [] -> Some []
| p :: ps ->
  (match parent p with
   | Some a ->
     let (_, deps) = a in
     (match gather_dependencies_with parent ps with
      | Some rest -> Some (app deps rest)
      | None -> None)
   | None -> None)

(** val infer_fo_with :
    (int -> clause option) -> (int -> clause option) -> (int -> annotated
    option) -> fo_rule -> annotated option **)

let infer_fo_with input components0 parent = function
| Ordinary primitive ->
  (match infer_with input (fun i -> option_map fst (parent i)) primitive with
   | Some c ->
     (match gather_dependencies_with parent (rule_parents primitive) with
      | Some deps -> Some (c, (fast_nodup deps))
      | None -> None)
   | None -> None)
| Component id ->
  (match components0 id with
   | Some c -> Some (c, (id :: []))
   | None -> None)

(** val index_replay_fo_from :
    (int -> clause option) -> (int -> clause option) -> annotated ClauseMap.t
    -> ClauseMap.key -> fo_step list -> annotated ClauseMap.t option **)

let rec index_replay_fo_from input components0 db next = function
| [] -> Some db
| f :: rest ->
  let (r, c) = f in
  (match infer_fo_with input components0 (fun i -> ClauseMap.find i db) r with
   | Some a ->
     let (expected, deps) = a in
     if included expected c
     then index_replay_fo_from input components0
            (ClauseMap.add next (c, deps) db) (Stdlib.Int.succ next) rest
     else None
   | None -> None)

type sat_literal = bool * int

type sat_clause = sat_literal list

(** val sat_equal : sat_literal -> sat_literal -> bool **)

let sat_equal x y =
  (&&) (eqb0 (fst x) (fst y)) ((=) (snd x) (snd y))

(** val sat_included : sat_clause -> sat_clause -> bool **)

let sat_included xs ys =
  forallb (fun x -> existsb (sat_equal x) ys) xs

(** val sat_remove : sat_literal -> sat_clause -> sat_literal list **)

let sat_remove l c =
  filter (fun x -> negb (sat_equal l x)) c

(** val sat_resolve : sat_clause -> int -> sat_clause -> sat_clause option **)

let sat_resolve left pivot right =
  if (&&) (existsb (sat_equal (true, pivot)) left)
       (existsb (sat_equal (false, pivot)) right)
  then Some
         (app (sat_remove (true, pivot) left)
           (sat_remove (false, pivot) right))
  else if (&&) (existsb (sat_equal (false, pivot)) left)
            (existsb (sat_equal (true, pivot)) right)
       then Some
              (app (sat_remove (false, pivot) left)
                (sat_remove (true, pivot) right))
       else None

(** val sat_index :
    sat_clause -> unit ClauseMap.t -> unit ClauseMap.t -> unit
    ClauseMap.t * unit ClauseMap.t **)

let rec sat_index ys positive0 negative =
  match ys with
  | [] -> (positive0, negative)
  | s :: ys0 ->
    let (sign, id) = s in
    if sign
    then sat_index ys0 (ClauseMap.add id () positive0) negative
    else sat_index ys0 positive0 (ClauseMap.add id () negative)

(** val indexed_sat_included : sat_clause -> sat_clause -> bool **)

let indexed_sat_included xs ys =
  let (positive0, negative) = sat_index ys ClauseMap.empty ClauseMap.empty in
  forallb (fun x ->
    ClauseMap.mem (snd x) (if fst x then positive0 else negative)) xs

(** val fast_sat_included : sat_clause -> sat_literal list -> bool **)

let fast_sat_included xs ys =
  if (<=) (length ys) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ
       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  then sat_included xs ys
  else indexed_sat_included xs ys

(** val collect_components_with :
    (int -> clause option) -> int list -> clause list option **)

let rec collect_components_with component = function
| [] -> Some []
| id :: ids0 ->
  (match component id with
   | Some c ->
     (match collect_components_with component ids0 with
      | Some cs -> Some (c :: cs)
      | None -> None)
   | None -> None)

(** val infer_split_with :
    (int -> clause option) -> (int -> annotated option) -> (int * int list) ->
    sat_clause option **)

let infer_split_with component fo = function
| (parent, ids) ->
  (match fo parent with
   | Some a ->
     let (c, deps) = a in
     (match collect_components_with component ids with
      | Some cs ->
        if (&&) ((&&) (included c (concat cs)) (included (concat cs) c))
             (components_disjoint cs)
        then Some
               (app (map (fun id -> (false, id)) deps)
                 (map (fun id -> (true, id)) ids))
        else None
      | None -> None)
   | None -> None)

(** val build_splits_with :
    (int -> clause option) -> (int -> annotated option) -> (int * int list)
    list -> sat_clause list option **)

let rec build_splits_with component fo = function
| [] -> Some []
| s :: ss ->
  (match infer_split_with component fo s with
   | Some c ->
     (match build_splits_with component fo ss with
      | Some cs -> Some (c :: cs)
      | None -> None)
   | None -> None)

type sat_rule =
| Split of int
| Conflict of int
| Boolean_resolve of int * int * int

type sat_step = sat_rule * sat_clause

(** val infer_conflict_with :
    (int -> annotated option) -> int -> sat_clause option **)

let infer_conflict_with fo id =
  match fo id with
  | Some a ->
    let (c, deps) = a in
    (match c with
     | [] -> Some (map (fun id0 -> (false, id0)) deps)
     | _ :: _ -> None)
  | None -> None

(** val infer_sat_with :
    (int -> annotated option) -> (int -> sat_clause option) -> (int ->
    sat_clause option) -> sat_rule -> sat_clause option **)

let infer_sat_with fo splits0 db = function
| Split id -> splits0 id
| Conflict id -> infer_conflict_with fo id
| Boolean_resolve (p, pivot, q) ->
  (match db p with
   | Some l ->
     (match db q with
      | Some r0 -> sat_resolve l pivot r0
      | None -> None)
   | None -> None)

(** val index_replay_sat_from :
    (int -> annotated option) -> (int -> sat_clause option) -> sat_clause
    ClauseMap.t -> ClauseMap.key -> sat_step list -> sat_clause ClauseMap.t
    option **)

let rec index_replay_sat_from fo splits0 db next = function
| [] -> Some db
| s :: rest ->
  let (r, c) = s in
  (match infer_sat_with fo splits0 (fun i -> ClauseMap.find i db) r with
   | Some expected ->
     if fast_sat_included expected c
     then index_replay_sat_from fo splits0 (ClauseMap.add next c db)
            (Stdlib.Int.succ next) rest
     else None
   | None -> None)

type certificate = { components : clause list; fo_steps : fo_step list;
                     splits : (int * int list) list;
                     boolean_steps : sat_step list; boolean_root : int }

(** val check : clause list -> certificate -> bool **)

let check inputs proof =
  let component = cached proof.components in
  (match index_replay_fo_from (cached inputs) component ClauseMap.empty 0
           proof.fo_steps with
   | Some fo ->
     (match build_splits_with component (fun i -> ClauseMap.find i fo)
              proof.splits with
      | Some split_clauses ->
        (match index_replay_sat_from (fun i -> ClauseMap.find i fo)
                 (cached split_clauses) ClauseMap.empty 0 proof.boolean_steps with
         | Some db ->
           (match ClauseMap.find proof.boolean_root db with
            | Some s -> (match s with
                         | [] -> true
                         | _ :: _ -> false)
            | None -> false)
         | None -> false)
      | None -> false)
   | None -> false)
