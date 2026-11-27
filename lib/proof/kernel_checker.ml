
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

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
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

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a :: l0 -> rev_append l0 (a :: l')

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

module PairOrderedType =
 functor (O1:OrderedType) ->
 functor (O2:OrderedType) ->
 struct
  module MO1 = OrderedTypeFacts(O1)

  module MO2 = OrderedTypeFacts(O2)

  type t = O1.t * O2.t

  (** val compare : t -> t -> (O1.t * O2.t) compare0 **)

  let compare x y =
    let (t0, t1) = x in
    let (t2, t3) = y in
    let c = O1.compare t0 t2 in
    (match c with
     | LT -> LT
     | EQ ->
       let c0 = O2.compare t1 t3 in
       (match c0 with
        | LT -> LT
        | EQ -> EQ
        | GT -> GT)
     | GT -> GT)

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match compare x y with
    | EQ -> true
    | _ -> false
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

type step = Rocq_checker.rule * clause

type certificate = step list

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

(** val empty_clause : clause -> bool **)

let empty_clause = function
| [] -> true
| _ :: _ -> false

(** val replay_indexed :
    (int -> clause option) -> clause ClauseMap.t -> ClauseMap.key -> bool ->
    (Rocq_checker.rule * clause) list -> bool **)

let rec replay_indexed input db next found = function
| [] -> found
| y :: rest ->
  let (r, c) = y in
  (match infer_with input (fun i -> ClauseMap.find i db) r with
   | Some expected ->
     if included expected c
     then replay_indexed input (ClauseMap.add next c db) (Stdlib.Int.succ
            next) ((||) found (empty_clause c)) rest
     else false
   | None -> false)

(** val check : clause list -> (Rocq_checker.rule * clause) list -> bool **)

let check inputs steps =
  replay_indexed (cached inputs) ClauseMap.empty 0 false steps

type fo_step = Avatar_checker.fo_rule * clause

type sat_literal = bool * int

type sat_clause = sat_literal list

type sat_step = Avatar_checker.sat_rule * sat_clause



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
  let z0 = Wire_types.F (Stdlib.Int.succ (Stdlib.Int.succ fresh)) in
  all_free (Stdlib.Int.succ (Stdlib.Int.succ fresh))
    (implication (substitute_formula 0 (Stdlib.Int.succ 0) z0 phi)
      (Wire_types.Eq (z0, (Wire_types.F (Stdlib.Int.succ 0)))))

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
    (unit -> bool) -> int -> 'a1 Source_checker.matrix -> 'a1 list list option **)

let rec bounded_cnf visit limit m =
  if visit ()
  then (match m with
        | Source_checker.MLiteral l ->
          bounded_identity limit ((l :: []) :: [])
        | Source_checker.MConj ms ->
          let rec join0 remaining = function
          | [] -> Some []
          | m0 :: ms1 ->
            (match bounded_cnf visit limit m0 with
             | Some xs ->
               if (<=) (length xs) remaining
               then (match join0
                             ((fun n m -> Stdlib.max 0 (n-m)) remaining
                               (length xs))
                             ms1 with
                     | Some ys -> Some (app xs ys)
                     | None -> None)
               else None
             | None -> None)
          in join0 limit ms
        | Source_checker.MDisj ms ->
          let rec join0 acc = function
          | [] -> bounded_identity limit acc
          | m0 :: ms1 ->
            (match bounded_cnf visit limit m0 with
             | Some ys ->
               (match bounded_distribute limit acc ys with
                | Some xs -> join0 xs ms1
                | None -> None)
             | None -> None)
          in join0 ([] :: []) ms)
  else None

(** val opposite :
    'a1 Source_checker.definition_literal -> 'a1
    Source_checker.definition_literal **)

let opposite = function
| Source_checker.DBase (b, a) -> Source_checker.DBase ((negb b), a)
| Source_checker.DAux (b, id, vs) -> Source_checker.DAux ((negb b), id, vs)

(** val definition_root :
    int -> 'a1 Source_checker.definition -> 'a1
    Source_checker.definition_literal **)

let definition_root id d =
  Source_checker.DAux (true, id, ((fun d -> d.Source_checker.arguments) d))

(** val definition_clauses :
    int -> 'a1 Source_checker.definition -> 'a1
    Source_checker.definition_literal list list **)

let definition_clauses id d =
  let root = definition_root id d in
  if (fun d -> d.Source_checker.conjunction) d
  then app
         (map (fun child -> (opposite root) :: (child :: []))
           ((fun d -> d.Source_checker.children) d))
         ((root :: (map opposite ((fun d -> d.Source_checker.children) d))) :: [])
  else app
         (((opposite root) :: ((fun d -> d.Source_checker.children) d)) :: [])
         (map (fun child -> root :: ((opposite child) :: []))
           ((fun d -> d.Source_checker.children) d))

(** val literal_variables :
    ('a1 -> int list) -> 'a1 Source_checker.definition_literal -> int list **)

let literal_variables support = function
| Source_checker.DBase (_, a) -> support a
| Source_checker.DAux (_, _, vs) -> vs

(** val literal_before :
    int -> 'a1 Source_checker.definition_literal -> bool **)

let literal_before limit = function
| Source_checker.DBase (_, _) -> true
| Source_checker.DAux (_, id, _) -> negb ((<=) limit id)

(** val definition_valid :
    ('a1 -> int list) -> int -> 'a1 Source_checker.definition -> bool **)

let definition_valid support id d =
  (&&) (forallb (literal_before id) ((fun d -> d.Source_checker.children) d))
    (forallb (fun v ->
      existsb ((=) v) ((fun d -> d.Source_checker.arguments) d))
      (flat_map (literal_variables support)
        ((fun d -> d.Source_checker.children) d)))

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
    (int -> 'a1 Source_checker.definition option) -> ('a1 -> int list) -> int
    -> bool **)

let rec valid_prefix lookup0 support size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun size0 ->
    (&&) (valid_prefix lookup0 support size0)
      (match lookup0 size0 with
       | Some d -> definition_valid support size0 d
       | None -> false))
    size

(** val match_connective :
    (int -> 'a1 Source_checker.definition option) -> bool -> ('a1
    Source_checker.definition_literal list -> bool) -> int -> 'a1
    Source_checker.definition_literal -> bool **)

let match_connective lookup0 expected check_children size = function
| Source_checker.DBase (_, _) -> false
| Source_checker.DAux (b, id, vars) ->
  if b
  then (&&) (negb ((<=) size id))
         (match lookup0 id with
          | Some d ->
            (&&)
              ((&&)
                (eqb0 expected ((fun d -> d.Source_checker.conjunction) d))
                (forallb2 (=) vars ((fun d -> d.Source_checker.arguments) d)))
              (check_children ((fun d -> d.Source_checker.children) d))
          | None -> false)
  else false

(** val matches_matrix :
    (int -> 'a1 Source_checker.definition option) -> ('a1 -> 'a1 -> bool) ->
    int -> (bool * 'a1) Source_checker.matrix -> 'a1
    Source_checker.definition_literal -> bool **)

let rec matches_matrix lookup0 equal0 size m root =
  match m with
  | Source_checker.MLiteral p ->
    let (sign, atom0) = p in
    (match root with
     | Source_checker.DBase (other, b) ->
       (&&) (eqb0 sign other) (equal0 atom0 b)
     | Source_checker.DAux (_, _, _) -> false)
  | Source_checker.MConj ms ->
    match_connective lookup0 true
      (forallb2 (matches_matrix lookup0 equal0 size) ms) size root
  | Source_checker.MDisj ms ->
    match_connective lookup0 false
      (forallb2 (matches_matrix lookup0 equal0 size) ms) size root

(** val emit_definitions :
    (int -> 'a1 Source_checker.definition option) -> (unit -> bool) -> int ->
    int -> int -> 'a1 Source_checker.definition_literal list list option **)

let rec emit_definitions lookup0 visit count first budget =
  if visit ()
  then ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Some [])
          (fun count0 ->
          match lookup0 first with
          | Some d ->
            if negb
                 ((<=) budget
                   (length ((fun d -> d.Source_checker.children) d)))
            then let cs = definition_clauses first d in
                 (match emit_definitions lookup0 visit count0 (Stdlib.Int.succ
                          first)
                          ((fun n m -> Stdlib.max 0 (n-m)) budget (length cs)) with
                  | Some rest -> Some (app cs rest)
                  | None -> None)
            else None
          | None -> None)
          count)
  else None

(** val checked_definitions :
    (int -> 'a1 Source_checker.definition option) -> (unit -> bool) -> ('a1 ->
    'a1 -> bool) -> ('a1 -> int list) -> int -> int -> (bool * 'a1)
    Source_checker.matrix -> 'a1 Source_checker.definition_literal -> 'a1
    Source_checker.definition_literal list list option **)

let checked_definitions lookup0 visit equal0 support size budget m root =
  if (&&)
       ((&&) ((&&) (visit ()) (valid_prefix lookup0 support size))
         (matches_matrix lookup0 equal0 size m root))
       ((<=) (Stdlib.Int.succ 0) budget)
  then (match emit_definitions lookup0 visit size 0
                ((fun n m -> Stdlib.max 0 (n-m)) budget (Stdlib.Int.succ 0)) with
        | Some cs -> Some (app cs ((root :: []) :: []))
        | None -> None)
  else None

(** val map_option0 : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec map_option0 f = function
| [] -> Some []
| x :: xs0 ->
  (match f x with
   | Some y ->
     (match map_option0 f xs0 with
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
          (match map_option0 (instantiate_bound visit apply env) ts with
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

let rec scope_list check0 next = function
| [] -> Some next
| x :: xs0 ->
  (match check0 next x with
   | Some after -> scope_list check0 after xs0
   | None -> None)

(** val erase_universals : 'a1 universal -> 'a1 Source_checker.matrix **)

let rec erase_universals = function
| ULiteral l -> Source_checker.MLiteral l
| UConj fs -> Source_checker.MConj (map erase_universals fs)
| UDisj fs -> Source_checker.MDisj (map erase_universals fs)
| UAll (_, f0) -> erase_universals f0

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
          (match map_option0 (instantiate_bound visit apply env) ts with
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
          then let term1 = variable next_v in
               (match eliminate_quantifiers visit apply variable witness
                        predicate equality limit (term1 :: env)
                        (app universals (term1 :: [])) (Stdlib.Int.succ
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

(** val term_variables : 'a1 Source_checker.wire_term -> (int * int) list **)

let rec term_variables = function
| Source_checker.V v -> v :: []
| Source_checker.Fn (_, ts) -> flat_map term_variables ts

(** val atom_variables :
    ('a1, 'a2) Source_checker.wire_atom -> (int * int) list **)

let atom_variables = function
| Source_checker.P (_, ts) -> flat_map term_variables ts
| Source_checker.E (x, y) -> app (term_variables x) (term_variables y)
| Source_checker.D (_, ts) -> flat_map term_variables ts

(** val term_indices_acc :
    'a1 Source_checker.wire_term -> int list -> int list **)

let rec term_indices_acc t0 acc =
  match t0 with
  | Source_checker.V p -> let (_, i) = p in i :: acc
  | Source_checker.Fn (_, ts) ->
    fold_left (fun acc0 t1 -> term_indices_acc t1 acc0) ts acc

(** val atom_indices_acc : ('a1, 'a2) Source_checker.wire_atom -> int list **)

let atom_indices_acc = function
| Source_checker.P (_, ts) ->
  fold_left (fun acc t0 -> term_indices_acc t0 acc) ts []
| Source_checker.E (x, y) -> term_indices_acc y (term_indices_acc x [])
| Source_checker.D (_, ts) ->
  fold_left (fun acc t0 -> term_indices_acc t0 acc) ts []

(** val wire_support : ('a1, 'a2) Source_checker.wire_atom -> int list **)

let wire_support a =
  sort_handles (atom_indices_acc a)

(** val local_variable : (int * int) -> bool **)

let local_variable v =
  (&&) ((=) (fst v) 0) ((<=) 0 (snd v))

(** val wire_term_local : 'a1 Source_checker.wire_term -> bool **)

let rec wire_term_local = function
| Source_checker.V v -> local_variable v
| Source_checker.Fn (_, ts) -> forallb wire_term_local ts

(** val wire_base_valid : ('a1, 'a2) Source_checker.wire_atom -> bool **)

let wire_base_valid = function
| Source_checker.P (_, ts) -> forallb wire_term_local ts
| Source_checker.E (x, y) -> (&&) (wire_term_local x) (wire_term_local y)
| Source_checker.D (_, _) -> false

(** val checked_wire_support :
    ('a1, 'a2) Source_checker.wire_atom -> int list option **)

let checked_wire_support a =
  if wire_base_valid a then Some (wire_support a) else None

type ('f, 'pT) wire_clause = ('f, 'pT) Source_checker.wire_literal list

(** val clause_variables : ('a1, 'a2) wire_clause -> (int * int) list **)

let clause_variables c =
  flat_map (fun l -> atom_variables ((fun l -> l.Source_checker.atom) l)) c

(** val rename_term :
    ((int * int) -> int * int) -> 'a1 Source_checker.wire_term -> 'a1
    Source_checker.wire_term **)

let rec rename_term rename = function
| Source_checker.V v -> Source_checker.V (rename v)
| Source_checker.Fn (s, ts) ->
  Source_checker.Fn (s, (map (rename_term rename) ts))

(** val rename_atom :
    ((int * int) -> int * int) -> ('a1, 'a2) Source_checker.wire_atom -> ('a1,
    'a2) Source_checker.wire_atom **)

let rename_atom rename = function
| Source_checker.P (p, ts) ->
  Source_checker.P (p, (map (rename_term rename) ts))
| Source_checker.E (x, y) ->
  Source_checker.E ((rename_term rename x), (rename_term rename y))
| Source_checker.D (id, ts) ->
  Source_checker.D (id, (map (rename_term rename) ts))

(** val rename_literal :
    ((int * int) -> int * int) -> ('a1, 'a2) Source_checker.wire_literal ->
    ('a1, 'a2) Source_checker.wire_literal **)

let rename_literal rename l =
  (fun (positive, atom) -> { Source_checker.positive; atom })
    (((fun l -> l.Source_checker.positive) l),
    (rename_atom rename ((fun l -> l.Source_checker.atom) l)))

(** val rename_clause :
    ((int * int) -> int * int) -> ('a1, 'a2) wire_clause -> ('a1, 'a2)
    Source_checker.wire_literal list **)

let rename_clause rename c =
  map (rename_literal rename) c

(** val wire_quantifiers :
    (unit -> bool) -> int -> int -> ('a1, 'a2) normal -> (bool * ('a1, 'a2)
    Source_checker.wire_atom) universal supplied option **)

let wire_quantifiers visit limit ax normal0 =
  eliminate_quantifiers visit (fun f ts -> Source_checker.Fn
    ((Source_checker.Original f), ts)) (fun i -> Source_checker.V (0, i))
    (fun id ts -> Source_checker.Fn ((Source_checker.Skolem (ax, id)), ts))
    (fun sign p ts -> (sign, (Source_checker.P (p, ts)))) (fun sign x y ->
    (sign, (Source_checker.E (x, y)))) limit [] [] 0 0 normal0

(** val wire_universal_scope :
    (unit -> bool) -> int list -> int -> int -> (bool * ('a1, 'a2)
    Source_checker.wire_atom) universal -> int option **)

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
    (unit -> bool) -> int -> (bool * ('a1, 'a2) Source_checker.wire_atom)
    universal -> (bool * ('a1, 'a2) Source_checker.wire_atom)
    Source_checker.matrix option **)

let wire_checked_universals visit limit f =
  match wire_universal_scope visit [] limit 0 f with
  | Some _ -> Some (erase_universals f)
  | None -> None

(** val pack_literal :
    (bool * ('a1, 'a2) Source_checker.wire_atom) -> ('a1, 'a2)
    Source_checker.wire_literal **)

let pack_literal l =
  (fun (positive, atom) -> { Source_checker.positive; atom }) ((fst l),
    (snd l))

(** val wire_distributive_cnf :
    (unit -> bool) -> int -> (bool * ('a1, 'a2) Source_checker.wire_atom)
    Source_checker.matrix -> ('a1, 'a2) Source_checker.wire_literal list list
    option **)

let wire_distributive_cnf visit budget m =
  match bounded_cnf visit budget m with
  | Some cs -> Some (map (map pack_literal) cs)
  | None -> None

(** val wire_definition_valid :
    ('a1, 'a2) Source_checker.wire_atom Source_checker.definition_literal ->
    bool **)

let wire_definition_valid = function
| Source_checker.DBase (_, a) -> wire_base_valid a
| Source_checker.DAux (_, id, vars) ->
  (&&) ((<=) 0 id) (forallb (fun v -> (<=) 0 v) vars)

(** val wire_lookup :
    (int -> ('a1, 'a2) Source_checker.wire_atom Source_checker.definition
    option) -> int -> ('a1, 'a2) Source_checker.wire_atom
    Source_checker.definition option **)

let wire_lookup lookup0 id =
  match lookup0 id with
  | Some d ->
    if forallb wire_definition_valid ((fun d -> d.Source_checker.children) d)
    then Some d
    else None
  | None -> None

(** val wire_definitions_valid :
    (int -> ('a1, 'a2) Source_checker.wire_atom Source_checker.definition
    option) -> int -> bool **)

let rec wire_definitions_valid lookup0 size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> true)
    (fun size0 ->
    if wire_definitions_valid lookup0 size0
    then (match wire_lookup lookup0 size0 with
          | Some _ -> true
          | None -> false)
    else false)
    size

(** val pack_definition :
    int -> ('a1, 'a2) Source_checker.wire_atom
    Source_checker.definition_literal -> ('a1, 'a2)
    Source_checker.wire_literal **)

let pack_definition ax = function
| Source_checker.DBase (sign, a) ->
  (fun (positive, atom) -> { Source_checker.positive; atom }) (sign, a)
| Source_checker.DAux (sign, id, vars) ->
  (fun (positive, atom) -> { Source_checker.positive; atom }) (sign,
    (Source_checker.D ((ax, id),
    (map (fun i -> Source_checker.V (0, i)) vars))))

(** val wire_definitional_cnf :
    (int -> ('a1, 'a2) Source_checker.wire_atom Source_checker.definition
    option) -> (unit -> bool) -> (('a1, 'a2) Source_checker.wire_atom -> ('a1,
    'a2) Source_checker.wire_atom -> bool) -> int -> int -> int ->
    (bool * ('a1, 'a2) Source_checker.wire_atom) Source_checker.matrix ->
    ('a1, 'a2) Source_checker.wire_atom Source_checker.definition_literal ->
    ('a1, 'a2) Source_checker.wire_literal list list option **)

let wire_definitional_cnf lookup0 visit equal0 size budget ax m root =
  if (&&) ((&&) (visit ()) (wire_definition_valid root))
       (wire_definitions_valid lookup0 size)
  then (match checked_definitions lookup0 visit equal0 wire_support size
                budget m root with
        | Some cs -> Some (map (map (pack_definition ax)) cs)
        | None -> None)
  else None

(** val variable_equal : (int * int) -> (int * int) -> bool **)

let variable_equal x y =
  (&&) ((=) (fst x) (fst y)) ((=) (snd x) (snd y))

(** val first_variables_acc :
    (int * int) list -> (int * int) list -> (int * int) list **)

let rec first_variables_acc vars seen =
  match vars with
  | [] -> seen
  | v :: vars0 ->
    first_variables_acc vars0
      (if existsb (variable_equal v) seen then seen else v :: seen)

(** val first_variables : (int * int) list -> (int * int) list **)

let first_variables vars =
  rev (first_variables_acc vars [])

(** val variable_index : (int * int) -> (int * int) list -> int option **)

let rec variable_index v = function
| [] -> None
| x :: vars0 ->
  if variable_equal v x
  then Some 0
  else option_map (fun x0 -> Stdlib.Int.succ x0) (variable_index v vars0)

(** val local_name : (int * int) list -> (int * int) -> int * int **)

let local_name vars v =
  (0, (match variable_index v vars with
       | Some i -> i
       | None -> 0))

module VariableOrder = PairOrderedType(Nat_as_OT)(Nat_as_OT)

module VariableMap = Make(VariableOrder)

(** val collect_variables :
    VariableMap.key list -> unit VariableMap.t -> VariableMap.key list ->
    VariableMap.key list **)

let rec collect_variables vars known seen =
  match vars with
  | [] -> seen
  | v :: rest ->
    if VariableMap.mem v known
    then collect_variables rest known seen
    else collect_variables rest (VariableMap.add v () known) (v :: seen)

(** val collected_variables : VariableMap.key list -> VariableMap.key list **)

let collected_variables vars =
  rev_append (collect_variables vars VariableMap.empty []) []

(** val index_variables : VariableMap.key list -> int -> int VariableMap.t **)

let rec index_variables vars offset =
  match vars with
  | [] -> VariableMap.empty
  | v :: rest ->
    VariableMap.add v offset (index_variables rest (Stdlib.Int.succ offset))

(** val indexed_name : int VariableMap.t -> VariableMap.key -> int * int **)

let indexed_name names v =
  (0, (match VariableMap.find v names with
       | Some i -> i
       | None -> 0))

module type WireOrder =
 sig
  type function_name

  type predicate_name

  val leb :
    (function_name, predicate_name) Source_checker.wire_literal ->
    (function_name, predicate_name) Source_checker.wire_literal -> bool

  val equal :
    (function_name, predicate_name) Source_checker.wire_literal ->
    (function_name, predicate_name) Source_checker.wire_literal -> bool
 end

module WireNormalize =
 functor (Order:WireOrder) ->
 struct
  module LiteralOrder =
   struct
    type t =
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal

    (** val leb :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal -> bool **)

    let leb =
      Order.leb
   end

  module LiteralSort = Sort(LiteralOrder)

  (** val unique_after :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list **)

  let rec unique_after previous = function
  | [] -> []
  | l :: rest ->
    if Order.equal previous l
    then unique_after previous rest
    else l :: (unique_after l rest)

  (** val unique_sorted :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list **)

  let unique_sorted = function
  | [] -> []
  | l :: rest -> l :: (unique_after l rest)

  (** val sort_clause :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list **)

  let sort_clause literals =
    unique_sorted (LiteralSort.sort literals)

  (** val normalize :
      int -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list option **)

  let normalize limit c =
    let ordered = sort_clause c in
    let occurrences = clause_variables ordered in
    if (<=) (length occurrences) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))
    then let vars = first_variables occurrences in
         if (<=) (length vars) limit
         then Some (sort_clause (rename_clause (local_name vars) ordered))
         else None
    else let vars = collected_variables occurrences in
         if (<=) (length vars) limit
         then let names = index_variables vars 0 in
              Some (sort_clause (rename_clause (indexed_name names) ordered))
         else None
 end

(** val symbol_equal :
    ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_symbol -> 'a1
    Source_checker.wire_symbol -> bool **)

let symbol_equal equal_function x y =
  match x with
  | Source_checker.Original f ->
    (match y with
     | Source_checker.Original g -> equal_function f g
     | Source_checker.Skolem (_, _) -> false)
  | Source_checker.Skolem (a, i) ->
    (match y with
     | Source_checker.Original _ -> false
     | Source_checker.Skolem (b, j) ->
       (&&) ((&&) ((<=) 0 a) ((<=) 0 i)) (variable_equal (a, i) (b, j)))

(** val predicate_equal :
    ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_predicate -> 'a1
    Source_checker.wire_predicate -> bool **)

let predicate_equal equal_predicate x y =
  match x with
  | Source_checker.Named p ->
    (match y with
     | Source_checker.Named q -> equal_predicate p q
     | Source_checker.Auxiliary _ -> false)
  | Source_checker.Auxiliary i ->
    (match y with
     | Source_checker.Named _ -> false
     | Source_checker.Auxiliary j ->
       (&&) ((&&) ((<=) 0 (fst i)) ((<=) 0 (snd i))) (variable_equal i j))

(** val encoded_term :
    ('a1 -> 'a1 -> bool) -> ((int * int) -> int) -> (int -> 'a1
    Source_checker.wire_symbol option) -> 'a1 Source_checker.wire_term ->
    Rocq_checker.term -> bool **)

let rec encoded_term equal_function encode_variable decode_function t0 numeric =
  match t0 with
  | Source_checker.V v ->
    (match numeric with
     | Rocq_checker.Var n ->
       (&&) ((&&) ((&&) ((<=) 0 (fst v)) ((<=) 0 (snd v))) ((<=) 0 n))
         ((=) (encode_variable v) n)
     | Rocq_checker.Fun (_, _) -> false)
  | Source_checker.Fn (s, ts) ->
    (match numeric with
     | Rocq_checker.Var _ -> false
     | Rocq_checker.Fun (n, args) ->
       (&&) ((<=) 0 n)
         (match decode_function n with
          | Some decoded ->
            (&&) (symbol_equal equal_function s decoded)
              (forallb2
                (encoded_term equal_function encode_variable decode_function)
                ts args)
          | None -> false))

(** val encoded_predicate :
    ('a1 -> 'a1 -> bool) -> (int -> 'a1 Source_checker.wire_predicate option)
    -> 'a1 Source_checker.wire_predicate -> int -> bool **)

let encoded_predicate equal_predicate decode_predicate p n =
  (&&) ((<=) 0 n)
    (match decode_predicate n with
     | Some decoded -> predicate_equal equal_predicate p decoded
     | None -> false)

(** val encoded_atom :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_atom -> Rocq_checker.atom -> bool **)

let encoded_atom equal_function equal_predicate encode_variable decode_function decode_predicate a numeric =
  match a with
  | Source_checker.P (p, ts) ->
    (match numeric with
     | Rocq_checker.Pred (n, args) ->
       (&&)
         (encoded_predicate equal_predicate decode_predicate
           (Source_checker.Named p) n)
         (forallb2
           (encoded_term equal_function encode_variable decode_function) ts
           args)
     | Rocq_checker.Eq0 (_, _) -> false)
  | Source_checker.E (x, y) ->
    (match numeric with
     | Rocq_checker.Pred (_, _) -> false
     | Rocq_checker.Eq0 (u, v) ->
       (&&) (encoded_term equal_function encode_variable decode_function x u)
         (encoded_term equal_function encode_variable decode_function y v))
  | Source_checker.D (id, ts) ->
    (match numeric with
     | Rocq_checker.Pred (n, args) ->
       (&&)
         (encoded_predicate equal_predicate decode_predicate
           (Source_checker.Auxiliary id) n)
         (forallb2
           (encoded_term equal_function encode_variable decode_function) ts
           args)
     | Rocq_checker.Eq0 (_, _) -> false)

(** val encoded_literal :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_literal -> literal -> bool **)

let encoded_literal equal_function equal_predicate encode_variable decode_function decode_predicate l numeric =
  (&&) (eqb0 ((fun l -> l.Source_checker.positive) l) (fst numeric))
    (encoded_atom equal_function equal_predicate encode_variable
      decode_function decode_predicate ((fun l -> l.Source_checker.atom) l)
      (snd numeric))

(** val encoded_clause :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_literal list -> literal list -> bool **)

let encoded_clause equal_function equal_predicate encode_variable decode_function decode_predicate =
  forallb2
    (encoded_literal equal_function equal_predicate encode_variable
      decode_function decode_predicate)

(** val encoded_inputs :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_literal list list -> literal list list -> bool **)

let encoded_inputs equal_function equal_predicate encode_variable decode_function decode_predicate =
  forallb2
    (encoded_clause equal_function equal_predicate encode_variable
      decode_function decode_predicate)

module WireRefutation =
 functor (Order:WireOrder) ->
 struct
  module Normalize = WireNormalize(Order)
 end

type ('f, 'pT) source_input = { source_id : int;
                                source_text : ('f, 'pT)
                                              Wire_types.source_formula;
                                source_matrix : (bool * ('f, 'pT)
                                                Source_checker.wire_atom)
                                                Source_checker.matrix;
                                source_clauses : ('f, 'pT) wire_clause list }

module SourceRefutation =
 functor (Order:WireOrder) ->
 struct
  module Refutation = WireRefutation(Order)

  module Normalize = Refutation.Normalize
 end

type formula = (string, string) Wire_types.source_formula

type term0 = string Wire_types.source_term

(** val term_equal : term0 -> term0 -> bool **)

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

(** val term_signature : (string * int) list -> term0 -> bool **)

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

(** val term_parameters : term0 -> int list **)

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

(** val signature_ok : Source_checker.theory -> formula -> bool **)

let signature_ok t0 f =
  (||) ((fun t -> t.Source_checker.unrestricted_signature) t0)
    (formula_signature ((fun t -> t.Source_checker.function_symbols) t0)
      ((fun t -> t.Source_checker.predicate_symbols) t0) f)

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

(** val validate_axiom :
    int -> Source_checker.theory -> Wire_types.axiom -> bool **)

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
           ((fun t -> t.Source_checker.fixed_axioms) t0))
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
           ((fun t -> t.Source_checker.fixed_axioms) t0))
     | Wire_types.Instance (key0, phi) ->
       (&&)
         ((&&)
           ((&&)
             (admitted ((fun t -> t.Source_checker.allowed_schemas) t0) key0)
             (formula_scoped 0 false phi))
           (signature_ok t0 phi))
         (match builtin key0 with
          | Some kind ->
            (match schema_expansion limit kind phi with
             | Some expected ->
               equivalent expected ((fun a -> a.Wire_types.formula) a)
             | None -> false)
          | None -> false)
     | Wire_types.Registered_instance (n, r, data) ->
       (&&)
         (admitted ((fun t -> t.Source_checker.allowed_schemas) t0)
           (Wire_types.Registered (n, r)))
         ((fun t -> t.Source_checker.registered_check) t0 n r data
           ((fun a -> a.Wire_types.formula) a)))

(** val wire_term_equal :
    string Source_checker.wire_term -> string Source_checker.wire_term -> bool **)

let rec wire_term_equal a b =
  match a with
  | Source_checker.V x ->
    (match b with
     | Source_checker.V y -> variable_equal x y
     | Source_checker.Fn (_, _) -> false)
  | Source_checker.Fn (f, xs) ->
    (match b with
     | Source_checker.V _ -> false
     | Source_checker.Fn (g, ys) ->
       (&&) (symbol_equal (=) f g) (forallb2 wire_term_equal xs ys))

(** val wire_atom_equal :
    (string, string) Source_checker.wire_atom -> (string, string)
    Source_checker.wire_atom -> bool **)

let wire_atom_equal a b =
  match a with
  | Source_checker.P (p, xs) ->
    (match b with
     | Source_checker.P (q, ys) ->
       (&&) ((=) p q) (forallb2 wire_term_equal xs ys)
     | _ -> false)
  | Source_checker.E (x, y) ->
    (match b with
     | Source_checker.E (u, v) ->
       (&&) (wire_term_equal x u) (wire_term_equal y v)
     | _ -> false)
  | Source_checker.D (x, xs) ->
    (match b with
     | Source_checker.D (y, ys) ->
       (&&) (variable_equal x y) (forallb2 wire_term_equal xs ys)
     | _ -> false)

type cnf_evidence =
| DistributiveEvidence
| DefinitionalEvidence of (string, string) Source_checker.wire_atom
                          Source_checker.definition list
   * (string, string) Source_checker.wire_atom
     Source_checker.definition_literal

type prepared_axiom = { original_axiom : Wire_types.axiom;
                        cnf_hint : cnf_evidence }

type certificate1 = { certificate_theory : string;
                      certificate_axioms : prepared_axiom list;
                      numeric_inputs : clause list;
                      numeric_proof : certificate }

(** val compile_input :
    (unit -> bool) -> int -> int -> prepared_axiom -> (string, string)
    source_input option **)

let compile_input visit limit budget a =
  let source = (fun a -> a.Wire_types.formula) a.original_axiom in
  let id = (fun a -> a.Wire_types.axiom_id) a.original_axiom in
  if (&&) ((<=) 0 id) (formula_scoped 0 true source)
  then (match wire_quantifiers visit limit id (nnf true source) with
        | Some r ->
          (match wire_checked_universals visit limit r.supplied_value with
           | Some m ->
             let clauses =
               match a.cnf_hint with
               | DistributiveEvidence -> wire_distributive_cnf visit budget m
               | DefinitionalEvidence (ds, root) ->
                 wire_definitional_cnf (cached ds) visit wire_atom_equal
                   (length ds) budget id m root
             in
             (match clauses with
              | Some cs ->
                Some { source_id = id; source_text = source; source_matrix =
                  m; source_clauses = cs }
              | None -> None)
           | None -> None)
        | None -> None)
  else None

(** val compile_inputs :
    (unit -> bool) -> int -> int -> prepared_axiom list -> (string, string)
    source_input list option **)

let rec compile_inputs visit limit budget = function
| [] -> Some []
| a :: axioms0 ->
  (match compile_input visit limit budget a with
   | Some input ->
     (match compile_inputs visit limit budget axioms0 with
      | Some inputs -> Some (input :: inputs)
      | None -> None)
   | None -> None)

(** val unique_from : unit ClauseMap.t -> ClauseMap.key list -> bool **)

let rec unique_from seen = function
| [] -> true
| i :: ids0 ->
  if ClauseMap.mem i seen
  then false
  else unique_from (ClauseMap.add i () seen) ids0

(** val fast_unique_ids : ClauseMap.key list -> bool **)

let fast_unique_ids ids =
  unique_from ClauseMap.empty ids

module Kernel =
 functor (Order:WireOrder with type function_name = string with type predicate_name = 
 string) ->
 struct
  module Sound = SourceRefutation(Order)

  module Normalize = Sound.Normalize

  (** val normalize_inputs :
      int -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list list option **)

  let rec normalize_inputs limit = function
  | [] -> Some []
  | c :: cs0 ->
    (match Normalize.normalize limit c with
     | Some result ->
       (match normalize_inputs limit cs0 with
        | Some results -> Some (result :: results)
        | None -> None)
     | None -> None)

  (** val check_sources :
      (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
      Source_checker.wire_symbol option) -> (int -> string
      Source_checker.wire_predicate option) -> certificate1 -> bool **)

  let check_sources visit limit budget encode_variable decode_function decode_predicate c =
    match compile_inputs visit limit budget c.certificate_axioms with
    | Some inputs ->
      (&&) (fast_unique_ids (map (fun s -> s.source_id) inputs))
        (match normalize_inputs limit
                 (flat_map (fun s -> s.source_clauses) inputs) with
         | Some normalized ->
           (&&)
             (encoded_inputs (=) (=) encode_variable decode_function
               decode_predicate normalized c.numeric_inputs)
             (check c.numeric_inputs c.numeric_proof)
         | None -> false)
    | None -> false

  (** val check :
      (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
      Source_checker.wire_symbol option) -> (int -> string
      Source_checker.wire_predicate option) -> Source_checker.theory ->
      certificate1 -> bool **)

  let check visit limit budget encode_variable decode_function decode_predicate t0 c =
    (&&)
      ((&&)
        ((=) ((fun t -> t.Source_checker.theory_name) t0)
          c.certificate_theory)
        (forallb (fun a -> validate_axiom limit t0 a.original_axiom)
          c.certificate_axioms))
      (check_sources visit limit budget encode_variable decode_function
        decode_predicate c)

  (** val avatar_check_sources :
      (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
      Source_checker.wire_symbol option) -> (int -> string
      Source_checker.wire_predicate option) -> certificate1 ->
      Avatar_checker.certificate -> bool **)

  let avatar_check_sources visit limit budget encode_variable decode_function decode_predicate c proof =
    match compile_inputs visit limit budget c.certificate_axioms with
    | Some inputs ->
      (&&) (fast_unique_ids (map (fun s -> s.source_id) inputs))
        (match normalize_inputs limit
                 (flat_map (fun s -> s.source_clauses) inputs) with
         | Some normalized ->
           (&&)
             (encoded_inputs (=) (=) encode_variable decode_function
               decode_predicate normalized c.numeric_inputs)
             (Avatar_checker.check c.numeric_inputs proof)
         | None -> false)
    | None -> false

  (** val avatar_check :
      (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
      Source_checker.wire_symbol option) -> (int -> string
      Source_checker.wire_predicate option) -> Source_checker.theory ->
      certificate1 -> Avatar_checker.certificate -> bool **)

  let avatar_check visit limit budget encode_variable decode_function decode_predicate t0 c proof =
    (&&)
      ((&&)
        ((=) ((fun t -> t.Source_checker.theory_name) t0)
          c.certificate_theory)
        (forallb (fun a -> validate_axiom limit t0 a.original_axiom)
          c.certificate_axioms))
      (avatar_check_sources visit limit budget encode_variable decode_function
        decode_predicate c proof)
 end
