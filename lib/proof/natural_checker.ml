
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

(** val mul : int -> int -> int **)

let rec mul = ( * )



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
  (** val pred : int -> int **)

  let pred n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun u -> u)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    (<=) (Stdlib.Int.succ n0) m

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val max : int -> int -> int **)

  let rec max n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n0

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2
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

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op (+) x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

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

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

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

module N =
 struct
  (** val add : int -> int -> int **)

  let add = (+)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : int -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p' -> shift true (loop n' p'))
        (fun p' -> shift false (loop n' p'))
        (fun _ -> one)
        p)
      n0
  in loop (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))

(** val ascii_of_N : int -> char **)

let ascii_of_N n0 =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> zero)
    (fun p -> ascii_of_pos p)
    n0

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b :: l' ->
  N.add (if b then 1 else 0) (N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : char -> int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n1 -> match l with
               | [] -> None
               | _ :: l' -> nth_error l' n1)
    n0

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

  let i2z n0 =
    n0
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

module ClauseMap = Make(Nat_as_OT)

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
  | Wire_types.Registered (n0, r) ->
    (match y with
     | Wire_types.Registered (m, s) -> (&&) ((=) n0 m) ((=) r s)
     | _ -> false)

(** val admitted : Wire_types.schema list -> Wire_types.schema -> bool **)

let admitted schemas kind =
  existsb (schema_equal kind) schemas

(** val signature_ok : Source_checker.theory -> formula -> bool **)

let signature_ok t0 f =
  (||) ((fun t -> t.Source_checker.unrestricted_signature) t0)
    (formula_signature ((fun t -> t.Source_checker.function_symbols) t0)
      ((fun t -> t.Source_checker.predicate_symbols) t0) f)

(** val parse : int -> int list -> (Wire_types.code * int list) option **)

let rec parse fuel words0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun fuel0 ->
    match words0 with
    | [] -> None
    | y :: rest ->
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         match rest with
         | [] -> None
         | n0 :: rest0 -> Some ((Wire_types.Number n0), rest0))
         (fun n0 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ ->
           match parse fuel0 rest with
           | Some p ->
             let (x, rest0) = p in
             (match parse fuel0 rest0 with
              | Some p0 ->
                let (y0, rest1) = p0 in
                Some ((Wire_types.Pair (x, y0)), rest1)
              | None -> None)
           | None -> None)
           (fun _ -> None)
           n0)
         y))
    fuel

(** val decode : int list -> Wire_types.code option **)

let decode words0 =
  match parse (length words0) words0 with
  | Some p -> let (c, l) = p in (match l with
                                 | [] -> Some c
                                 | _ :: _ -> None)
  | None -> None

(** val list_code :
    ('a1 -> Wire_types.code) -> 'a1 list -> Wire_types.code **)

let rec list_code write = function
| [] -> Wire_types.Number 0
| x :: xs0 -> Wire_types.Pair ((write x), (list_code write xs0))

(** val list_value :
    (Wire_types.code -> 'a1 option) -> Wire_types.code -> 'a1 list option **)

let rec list_value read = function
| Wire_types.Number n0 ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some [])
     (fun _ -> None)
     n0)
| Wire_types.Pair (x, xs) ->
  (match read x with
   | Some x0 ->
     (match list_value read xs with
      | Some xs0 -> Some (x0 :: xs0)
      | None -> None)
   | None -> None)

(** val number_value : Wire_types.code -> int option **)

let number_value = function
| Wire_types.Number n0 -> Some n0
| Wire_types.Pair (_, _) -> None

(** val string_code : string -> Wire_types.code **)

let rec string_code s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> Wire_types.Number 0)
    (fun x xs -> Wire_types.Pair ((Wire_types.Number (nat_of_ascii x)),
    (string_code xs)))
    s

(** val string_value : Wire_types.code -> string option **)

let rec string_value = function
| Wire_types.Number n0 ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some "")
     (fun _ -> None)
     n0)
| Wire_types.Pair (left, xs) ->
  (match left with
   | Wire_types.Number x ->
     (match string_value xs with
      | Some s ->
        Some
          ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

          ((ascii_of_nat x), s))
      | None -> None)
   | Wire_types.Pair (_, _) -> None)

(** val term_code : string Wire_types.source_term -> Wire_types.code **)

let rec term_code = function
| Wire_types.B n0 ->
  Wire_types.Pair ((Wire_types.Number 0), (Wire_types.Number n0))
| Wire_types.F n0 ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ 0)), (Wire_types.Number
    n0))
| Wire_types.App (f, ts) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (Wire_types.Pair ((string_code f), (list_code term_code ts))))

(** val term_value :
    Wire_types.code -> string Wire_types.source_term option **)

let rec term_value = function
| Wire_types.Number _ -> None
| Wire_types.Pair (left, right) ->
  (match left with
   | Wire_types.Number n0 ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        match right with
        | Wire_types.Number n1 -> Some (Wire_types.B n1)
        | Wire_types.Pair (_, _) -> None)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          match right with
          | Wire_types.Number n2 -> Some (Wire_types.F n2)
          | Wire_types.Pair (_, _) -> None)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            match right with
            | Wire_types.Number _ -> None
            | Wire_types.Pair (f, ts) ->
              (match string_value f with
               | Some f0 ->
                 (match list_value term_value ts with
                  | Some ts0 -> Some (Wire_types.App (f0, ts0))
                  | None -> None)
               | None -> None))
            (fun _ -> None)
            n2)
          n1)
        n0)
   | Wire_types.Pair (_, _) -> None)

(** val source_code :
    (string, string) Wire_types.source_formula -> Wire_types.code **)

let rec source_code = function
| Wire_types.Top -> Wire_types.Number 0
| Wire_types.Bot -> Wire_types.Number (Stdlib.Int.succ 0)
| Wire_types.Pred (p, ts) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (Wire_types.Pair ((string_code p), (list_code term_code ts))))
| Wire_types.Eq (x, y) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Wire_types.Pair ((term_code x), (term_code y))))
| Wire_types.Neg f0 ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (source_code f0))
| Wire_types.Conj fs ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))),
    (list_code source_code fs))
| Wire_types.Disj fs ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (list_code source_code fs))
| Wire_types.All f0 ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (source_code f0))
| Wire_types.Ex f0 ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (source_code f0))

(** val source_value :
    Wire_types.code -> (string, string) Wire_types.source_formula option **)

let rec source_value = function
| Wire_types.Number n0 ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some Wire_types.Top)
     (fun n1 ->
     (fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some Wire_types.Bot)
       (fun _ -> None)
       n1)
     n0)
| Wire_types.Pair (left, f) ->
  (match left with
   | Wire_types.Number n0 ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            match f with
            | Wire_types.Number _ -> None
            | Wire_types.Pair (p, ts) ->
              (match string_value p with
               | Some p0 ->
                 (match list_value term_value ts with
                  | Some ts0 -> Some (Wire_types.Pred (p0, ts0))
                  | None -> None)
               | None -> None))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              match f with
              | Wire_types.Number _ -> None
              | Wire_types.Pair (x, y) ->
                (match term_value x with
                 | Some x0 ->
                   (match term_value y with
                    | Some y0 -> Some (Wire_types.Eq (x0, y0))
                    | None -> None)
                 | None -> None))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                option_map (fun x -> Wire_types.Neg x) (source_value f))
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ ->
                  option_map (fun x -> Wire_types.Conj x)
                    (list_value source_value f))
                  (fun n6 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ ->
                    option_map (fun x -> Wire_types.Disj x)
                      (list_value source_value f))
                    (fun n7 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ ->
                      option_map (fun x -> Wire_types.All x) (source_value f))
                      (fun n8 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ ->
                        option_map (fun x -> Wire_types.Ex x) (source_value f))
                        (fun _ -> None)
                        n8)
                      n7)
                    n6)
                  n5)
                n4)
              n3)
            n2)
          n1)
        n0)
   | Wire_types.Pair (_, _) -> None)

(** val schema_code : Wire_types.schema -> Wire_types.code **)

let schema_code = function
| Wire_types.Comprehension -> Wire_types.Number 0
| Wire_types.Separation -> Wire_types.Number (Stdlib.Int.succ 0)
| Wire_types.Replacement ->
  Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ 0))
| Wire_types.Unrestricted_separation ->
  Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| Wire_types.Registered (n0, r) ->
  Wire_types.Pair ((string_code n0), (string_code r))

(** val schema_value : Wire_types.code -> Wire_types.schema option **)

let schema_value = function
| Wire_types.Number n0 ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some Wire_types.Comprehension)
     (fun n1 ->
     (fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some Wire_types.Separation)
       (fun n2 ->
       (fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> Some Wire_types.Replacement)
         (fun n3 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> Some Wire_types.Unrestricted_separation)
           (fun _ -> None)
           n3)
         n2)
       n1)
     n0)
| Wire_types.Pair (n0, r) ->
  (match string_value n0 with
   | Some n1 ->
     (match string_value r with
      | Some r0 -> Some (Wire_types.Registered (n1, r0))
      | None -> None)
   | None -> None)

type term0 =
| Var of int
| Fun of string * term0 list

type form =
| Bot
| Atom of string option * term0 list
| Imp of form * form
| All of form

(** val neg : form -> form **)

let neg a =
  Imp (a, Bot)

(** val push : 'a1 -> (int -> 'a1) -> int -> 'a1 **)

let push x rho i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun i0 -> rho i0)
    i

(** val subst_term : (int -> term0) -> term0 -> term0 **)

let rec subst_term sigma = function
| Var i -> sigma i
| Fun (f, ts) -> Fun (f, (map (subst_term sigma) ts))

(** val shift_term : term0 -> term0 **)

let shift_term =
  subst_term (fun i -> Var (Stdlib.Int.succ i))

(** val up : (int -> term0) -> int -> term0 **)

let up sigma i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Var 0)
    (fun i0 -> shift_term (sigma i0))
    i

(** val subst : (int -> term0) -> form -> form **)

let rec subst sigma = function
| Bot -> Bot
| Atom (p, ts) -> Atom (p, (map (subst_term sigma) ts))
| Imp (a0, b) -> Imp ((subst sigma a0), (subst sigma b))
| All a0 -> All (subst (up sigma) a0)

(** val shift0 : form -> form **)

let shift0 =
  subst (fun i -> Var (Stdlib.Int.succ i))

(** val instantiate : term0 -> form -> form **)

let instantiate t0 =
  subst (push t0 (fun x -> Var x))

(** val maximum : int list -> int **)

let maximum =
  fold_right Nat.max 0

(** val term_bound : term0 -> int **)

let rec term_bound = function
| Var i -> Stdlib.Int.succ i
| Fun (_, ts) -> maximum (map term_bound ts)

(** val bound : form -> int **)

let rec bound = function
| Bot -> 0
| Atom (_, ts) -> maximum (map term_bound ts)
| Imp (a0, b) -> Nat.max (bound a0) (bound b)
| All a0 -> Nat.pred (bound a0)

(** val capture : int -> form -> form **)

let rec capture n0 a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> a)
    (fun n1 -> All (capture n1 a))
    n0

(** val close : form -> form **)

let close a =
  capture (bound a) a

(** val term_code0 : term0 -> Wire_types.code **)

let rec term_code0 = function
| Var i -> Wire_types.Number i
| Fun (f, ts) -> Wire_types.Pair ((string_code f), (list_code term_code0 ts))

(** val term_value0 : Wire_types.code -> term0 option **)

let rec term_value0 = function
| Wire_types.Number i -> Some (Var i)
| Wire_types.Pair (f, ts) ->
  (match string_value f with
   | Some f0 ->
     (match list_value term_value0 ts with
      | Some ts0 -> Some (Fun (f0, ts0))
      | None -> None)
   | None -> None)

(** val form_code : form -> Wire_types.code **)

let rec form_code = function
| Bot -> Wire_types.Number 0
| Atom (name, ts) ->
  (match name with
   | Some p ->
     Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
       0))), (Wire_types.Pair ((string_code p), (list_code term_code0 ts))))
   | None ->
     Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ 0)),
       (list_code term_code0 ts)))
| Imp (a0, b) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Wire_types.Pair ((form_code a0), (form_code b))))
| All a0 ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (form_code a0))

(** val form_value : Wire_types.code -> form option **)

let rec form_value = function
| Wire_types.Number n0 ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some Bot)
     (fun _ -> None)
     n0)
| Wire_types.Pair (left, a) ->
  (match left with
   | Wire_types.Number n0 ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          option_map (fun x -> Atom (None, x)) (list_value term_value0 a))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            match a with
            | Wire_types.Number _ -> None
            | Wire_types.Pair (p, ts) ->
              (match string_value p with
               | Some p0 ->
                 (match list_value term_value0 ts with
                  | Some ts0 -> Some (Atom ((Some p0), ts0))
                  | None -> None)
               | None -> None))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              match a with
              | Wire_types.Number _ -> None
              | Wire_types.Pair (a0, b) ->
                (match form_value a0 with
                 | Some a1 ->
                   (match form_value b with
                    | Some b0 -> Some (Imp (a1, b0))
                    | None -> None)
                 | None -> None))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> option_map (fun x -> All x) (form_value a))
                (fun _ -> None)
                n4)
              n3)
            n2)
          n1)
        n0)
   | Wire_types.Pair (_, _) -> None)

(** val code_dec : Wire_types.code -> Wire_types.code -> bool **)

let rec code_dec c x0 =
  match c with
  | Wire_types.Number n0 ->
    (match x0 with
     | Wire_types.Number n1 -> (=) n0 n1
     | Wire_types.Pair (_, _) -> false)
  | Wire_types.Pair (left, right) ->
    (match x0 with
     | Wire_types.Number _ -> false
     | Wire_types.Pair (left0, right0) ->
       if code_dec left left0 then code_dec right right0 else false)

(** val form_dec : form -> form -> bool **)

let form_dec a b =
  code_dec (form_code a) (form_code b)

type proof =
| Assume of int
| ImplicationIntroduction of form * proof
| ImplicationElimination of proof * proof
| UniversalIntroduction of proof
| UniversalElimination of term0 * proof
| Explosion of form * proof
| Peirce of form * form

(** val infer : form list -> proof -> form option **)

let rec infer g = function
| Assume i -> nth_error g i
| ImplicationIntroduction (a, p0) ->
  option_map (fun x -> Imp (a, x)) (infer (a :: g) p0)
| ImplicationElimination (p0, q) ->
  (match infer g p0 with
   | Some f ->
     (match f with
      | Imp (a, b) ->
        (match infer g q with
         | Some a' -> if form_dec a a' then Some b else None
         | None -> None)
      | _ -> None)
   | None -> None)
| UniversalIntroduction p0 ->
  option_map (fun x -> All x) (infer (map shift0 g) p0)
| UniversalElimination (t0, p0) ->
  (match infer g p0 with
   | Some f -> (match f with
                | All a -> Some (instantiate t0 a)
                | _ -> None)
   | None -> None)
| Explosion (a, p0) ->
  (match infer g p0 with
   | Some f -> (match f with
                | Bot -> Some a
                | _ -> None)
   | None -> None)
| Peirce (a, b) -> Some (Imp ((Imp ((Imp (a, b)), a)), a))

(** val context_at : ('a1 -> form option) -> 'a1 list -> form list option **)

let rec context_at axiom_at0 = function
| [] -> Some []
| i :: ids0 ->
  (match axiom_at0 i with
   | Some a ->
     (match context_at axiom_at0 ids0 with
      | Some g -> Some (a :: g)
      | None -> None)
   | None -> None)

type 'witness certificate = { assumptions : 'witness list; deduction : proof }

(** val check : ('a1 -> form option) -> 'a1 certificate -> bool **)

let check axiom_at0 c =
  match context_at axiom_at0 c.assumptions with
  | Some g ->
    (match infer g c.deduction with
     | Some f -> (match f with
                  | Bot -> true
                  | _ -> false)
     | None -> false)
  | None -> false

(** val words : int -> int -> int list list **)

let rec words alphabet length0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [] :: [])
    (fun length1 ->
    flat_map (fun x -> map (fun x0 -> x :: x0) (words alphabet length1))
      (seq 0 alphabet))
    length0

(** val stage : int -> int list list **)

let stage n0 =
  flat_map (words (Stdlib.Int.succ n0)) (seq 0 (Stdlib.Int.succ n0))

(** val attempt :
    (int list -> 'a1 option) -> (int -> 'a1 -> bool) -> int -> int list -> 'a1
    option **)

let attempt decode0 check0 budget code0 =
  match decode0 code0 with
  | Some c -> if check0 budget c then Some c else None
  | None -> None

(** val first_success :
    (int list -> 'a1 option) -> (int -> 'a1 -> bool) -> (int * int list) list
    -> 'a1 option **)

let rec first_success decode0 check0 = function
| [] -> None
| p :: rest ->
  let (budget, code0) = p in
  (match attempt decode0 check0 budget code0 with
   | Some c -> Some c
   | None -> first_success decode0 check0 rest)

(** val jobs : int -> (int * int list) list **)

let jobs n0 =
  flat_map (fun budget -> map (fun x -> (budget, x)) (stage n0))
    (seq 0 (Stdlib.Int.succ n0))

(** val search :
    (int list -> 'a1 option) -> (int -> 'a1 -> bool) -> int -> 'a1 option **)

let search decode0 check0 n0 =
  first_success decode0 check0 (jobs n0)

(** val named_predicate : string -> term0 list -> form **)

let named_predicate p ts =
  Atom ((Some p), ts)

(** val default_term : term0 **)

let default_term =
  Fun ("", [])

(** val equal0 : term0 -> term0 -> form **)

let equal0 x y =
  Atom (None, (x :: (y :: [])))

(** val conjunction : form -> form -> form **)

let conjunction a b =
  neg (Imp (a, (neg b)))

(** val disjunction : form -> form -> form **)

let disjunction a b =
  Imp ((neg a), b)

(** val truth : form **)

let truth =
  Imp (Bot, Bot)

(** val translate_term : int -> string Wire_types.source_term -> term0 **)

let rec translate_term depth = function
| Wire_types.B i -> if Nat.ltb i depth then Var i else default_term
| Wire_types.F _ -> default_term
| Wire_types.App (f, ts) -> Fun (f, (map (translate_term depth) ts))

(** val translate :
    int -> (string, string) Wire_types.source_formula -> form **)

let rec translate depth = function
| Wire_types.Top -> truth
| Wire_types.Bot -> Bot
| Wire_types.Pred (p, ts) -> named_predicate p (map (translate_term depth) ts)
| Wire_types.Eq (x, y) ->
  equal0 (translate_term depth x) (translate_term depth y)
| Wire_types.Neg f0 -> neg (translate depth f0)
| Wire_types.Conj fs ->
  let rec all = function
  | [] -> truth
  | f0 :: fs1 -> conjunction (translate depth f0) (all fs1)
  in all fs
| Wire_types.Disj fs ->
  let rec some = function
  | [] -> Bot
  | f0 :: fs1 -> disjunction (translate depth f0) (some fs1)
  in some fs
| Wire_types.All f0 -> All (translate (Stdlib.Int.succ depth) f0)
| Wire_types.Ex f0 -> neg (All (neg (translate (Stdlib.Int.succ depth) f0)))

(** val source_sentence :
    (string, string) Wire_types.source_formula -> form **)

let source_sentence f =
  close (translate 0 f)

(** val equal_arguments : term0 list -> term0 list -> form **)

let rec equal_arguments xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> truth
           | _ :: _ -> Bot)
  | x :: xs0 ->
    (match ys with
     | [] -> Bot
     | y :: ys0 -> conjunction (equal0 x y) (equal_arguments xs0 ys0))

type permission =
| FixedPermission of int
| SchemaPermission of Wire_types.schema * int list * int * formula
| RegisteredPermission of string * string * string * formula
| EquivalentPermission of permission * formula

(** val authorize : Source_checker.theory -> permission -> formula option **)

let rec authorize t0 = function
| FixedPermission i ->
  option_map (fun a -> a.Wire_types.formula)
    (nth_error ((fun t -> t.Source_checker.fixed_axioms) t0) i)
| SchemaPermission (key0, variables, fresh, phi) ->
  if (&&) (admitted ((fun t -> t.Source_checker.allowed_schemas) t0) key0)
       (signature_ok t0 phi)
  then (match builtin key0 with
        | Some kind -> checked_schema kind "member" variables fresh phi
        | None -> None)
  else None
| RegisteredPermission (n0, r, data, f) ->
  if (&&)
       ((&&)
         ((&&)
           (admitted ((fun t -> t.Source_checker.allowed_schemas) t0)
             (Wire_types.Registered (n0, r)))
           (formula_scoped 0 true f))
         (signature_ok t0 f))
       ((fun t -> t.Source_checker.registered_check) t0 n0 r data f)
  then Some f
  else None
| EquivalentPermission (p0, f) ->
  (match authorize t0 p0 with
   | Some a -> if equivalent a f then Some f else None
   | None -> None)

(** val permission_code : permission -> Wire_types.code **)

let rec permission_code = function
| FixedPermission i ->
  Wire_types.Pair ((Wire_types.Number 0), (Wire_types.Number i))
| SchemaPermission (key0, variables, fresh, phi) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ 0)), (Wire_types.Pair
    ((schema_code key0), (Wire_types.Pair
    ((list_code (fun x -> Wire_types.Number x) variables), (Wire_types.Pair
    ((Wire_types.Number fresh), (source_code phi))))))))
| RegisteredPermission (n0, r, data, f) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (Wire_types.Pair ((string_code n0), (Wire_types.Pair ((string_code r),
    (Wire_types.Pair ((string_code data), (source_code f))))))))
| EquivalentPermission (p0, f) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Wire_types.Pair ((permission_code p0),
    (source_code f))))

(** val permission_value : Wire_types.code -> permission option **)

let rec permission_value = function
| Wire_types.Number _ -> None
| Wire_types.Pair (left, right) ->
  (match left with
   | Wire_types.Number n0 ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        match right with
        | Wire_types.Number i -> Some (FixedPermission i)
        | Wire_types.Pair (_, _) -> None)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          match right with
          | Wire_types.Number _ -> None
          | Wire_types.Pair (key0, right0) ->
            (match right0 with
             | Wire_types.Number _ -> None
             | Wire_types.Pair (variables, right1) ->
               (match right1 with
                | Wire_types.Number _ -> None
                | Wire_types.Pair (left0, phi) ->
                  (match left0 with
                   | Wire_types.Number fresh ->
                     (match schema_value key0 with
                      | Some key1 ->
                        (match list_value number_value variables with
                         | Some variables0 ->
                           (match source_value phi with
                            | Some phi0 ->
                              Some (SchemaPermission (key1, variables0, fresh,
                                phi0))
                            | None -> None)
                         | None -> None)
                      | None -> None)
                   | Wire_types.Pair (_, _) -> None))))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            match right with
            | Wire_types.Number _ -> None
            | Wire_types.Pair (n3, right0) ->
              (match right0 with
               | Wire_types.Number _ -> None
               | Wire_types.Pair (r, right1) ->
                 (match right1 with
                  | Wire_types.Number _ -> None
                  | Wire_types.Pair (data, f) ->
                    (match string_value n3 with
                     | Some n4 ->
                       (match string_value r with
                        | Some r0 ->
                          (match string_value data with
                           | Some data0 ->
                             (match source_value f with
                              | Some f0 ->
                                Some (RegisteredPermission (n4, r0, data0,
                                  f0))
                              | None -> None)
                           | None -> None)
                        | None -> None)
                     | None -> None))))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              match right with
              | Wire_types.Number _ -> None
              | Wire_types.Pair (p, f) ->
                (match permission_value p with
                 | Some p0 ->
                   (match source_value f with
                    | Some f0 -> Some (EquivalentPermission (p0, f0))
                    | None -> None)
                 | None -> None))
              (fun _ -> None)
              n3)
            n2)
          n1)
        n0)
   | Wire_types.Pair (_, _) -> None)

(** val fol_term_code : term0 -> Wire_types.code **)

let fol_term_code =
  term_code0

(** val fol_term_value : Wire_types.code -> term0 option **)

let fol_term_value =
  term_value0

(** val fol_formula_code : form -> Wire_types.code **)

let fol_formula_code =
  form_code

(** val fol_formula_value : Wire_types.code -> form option **)

let fol_formula_value =
  form_value

type equality_witness =
| Refl of term0
| Sym of term0 * term0
| Trans of term0 * term0 * term0
| Function of string * term0 list * term0 list
| Predicate of string * term0 list * term0 list

(** val equality_formula : equality_witness -> form **)

let equality_formula = function
| Refl t0 -> equal0 t0 t0
| Sym (t0, u) -> Imp ((equal0 t0 u), (equal0 u t0))
| Trans (t0, u, v) -> Imp ((equal0 t0 u), (Imp ((equal0 u v), (equal0 t0 v))))
| Function (f, xs, ys) ->
  Imp ((equal_arguments xs ys), (equal0 (Fun (f, xs)) (Fun (f, ys))))
| Predicate (p, xs, ys) ->
  Imp ((equal_arguments xs ys), (Imp ((named_predicate p xs),
    (named_predicate p ys))))

(** val equality_code : equality_witness -> Wire_types.code **)

let equality_code = function
| Refl t0 -> Wire_types.Pair ((Wire_types.Number 0), (fol_term_code t0))
| Sym (t0, u) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ 0)), (Wire_types.Pair
    ((fol_term_code t0), (fol_term_code u))))
| Trans (t0, u, v) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (Wire_types.Pair ((fol_term_code t0), (Wire_types.Pair ((fol_term_code u),
    (fol_term_code v))))))
| Function (f, xs, ys) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Wire_types.Pair ((string_code f),
    (Wire_types.Pair ((list_code fol_term_code xs),
    (list_code fol_term_code ys))))))
| Predicate (p, xs, ys) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (Wire_types.Pair
    ((string_code p), (Wire_types.Pair ((list_code fol_term_code xs),
    (list_code fol_term_code ys))))))

(** val equality_value : Wire_types.code -> equality_witness option **)

let equality_value = function
| Wire_types.Number _ -> None
| Wire_types.Pair (left, t0) ->
  (match left with
   | Wire_types.Number n0 ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> option_map (fun x -> Refl x) (fol_term_value t0))
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          match t0 with
          | Wire_types.Number _ -> None
          | Wire_types.Pair (t1, u) ->
            (match fol_term_value t1 with
             | Some t2 ->
               (match fol_term_value u with
                | Some u0 -> Some (Sym (t2, u0))
                | None -> None)
             | None -> None))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            match t0 with
            | Wire_types.Number _ -> None
            | Wire_types.Pair (t1, right) ->
              (match right with
               | Wire_types.Number _ -> None
               | Wire_types.Pair (u, v) ->
                 (match fol_term_value t1 with
                  | Some t2 ->
                    (match fol_term_value u with
                     | Some u0 ->
                       (match fol_term_value v with
                        | Some v0 -> Some (Trans (t2, u0, v0))
                        | None -> None)
                     | None -> None)
                  | None -> None)))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              match t0 with
              | Wire_types.Number _ -> None
              | Wire_types.Pair (f, right) ->
                (match right with
                 | Wire_types.Number _ -> None
                 | Wire_types.Pair (xs, ys) ->
                   (match string_value f with
                    | Some f0 ->
                      (match list_value fol_term_value xs with
                       | Some xs0 ->
                         (match list_value fol_term_value ys with
                          | Some ys0 -> Some (Function (f0, xs0, ys0))
                          | None -> None)
                       | None -> None)
                    | None -> None)))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                match t0 with
                | Wire_types.Number _ -> None
                | Wire_types.Pair (p, right) ->
                  (match right with
                   | Wire_types.Number _ -> None
                   | Wire_types.Pair (xs, ys) ->
                     (match string_value p with
                      | Some p0 ->
                        (match list_value fol_term_value xs with
                         | Some xs0 ->
                           (match list_value fol_term_value ys with
                            | Some ys0 -> Some (Predicate (p0, xs0, ys0))
                            | None -> None)
                         | None -> None)
                      | None -> None)))
                (fun _ -> None)
                n4)
              n3)
            n2)
          n1)
        n0)
   | Wire_types.Pair (_, _) -> None)

(** val axiom_at : Source_checker.theory -> Wire_types.code -> form option **)

let axiom_at t0 = function
| Wire_types.Number _ -> None
| Wire_types.Pair (left, w) ->
  (match left with
   | Wire_types.Number n0 ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        match permission_value w with
        | Some p -> option_map source_sentence (authorize t0 p)
        | None -> None)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          option_map (fun w0 -> close (equality_formula w0))
            (equality_value w))
          (fun _ -> None)
          n1)
        n0)
   | Wire_types.Pair (_, _) -> None)

(** val proof_code : proof -> Wire_types.code **)

let rec proof_code = function
| Assume n0 -> Wire_types.Pair ((Wire_types.Number 0), (Wire_types.Number n0))
| ImplicationIntroduction (a, p0) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ 0)), (Wire_types.Pair
    ((fol_formula_code a), (proof_code p0))))
| ImplicationElimination (p0, q) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (Wire_types.Pair ((proof_code p0), (proof_code q))))
| UniversalIntroduction p0 ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (proof_code p0))
| UniversalElimination (t0, p0) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (Wire_types.Pair
    ((fol_term_code t0), (proof_code p0))))
| Explosion (a, p0) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))),
    (Wire_types.Pair ((fol_formula_code a), (proof_code p0))))
| Peirce (a, b) ->
  Wire_types.Pair ((Wire_types.Number (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (Wire_types.Pair ((fol_formula_code a), (fol_formula_code b))))

(** val proof_value : Wire_types.code -> proof option **)

let rec proof_value = function
| Wire_types.Number _ -> None
| Wire_types.Pair (left, p) ->
  (match left with
   | Wire_types.Number n0 ->
     ((fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        match p with
        | Wire_types.Number n1 -> Some (Assume n1)
        | Wire_types.Pair (_, _) -> None)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          match p with
          | Wire_types.Number _ -> None
          | Wire_types.Pair (a, p0) ->
            (match fol_formula_value a with
             | Some a0 ->
               (match proof_value p0 with
                | Some p1 -> Some (ImplicationIntroduction (a0, p1))
                | None -> None)
             | None -> None))
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            match p with
            | Wire_types.Number _ -> None
            | Wire_types.Pair (p0, q) ->
              (match proof_value p0 with
               | Some p1 ->
                 (match proof_value q with
                  | Some q0 -> Some (ImplicationElimination (p1, q0))
                  | None -> None)
               | None -> None))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              option_map (fun x -> UniversalIntroduction x) (proof_value p))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                match p with
                | Wire_types.Number _ -> None
                | Wire_types.Pair (t0, p0) ->
                  (match fol_term_value t0 with
                   | Some t1 ->
                     (match proof_value p0 with
                      | Some p1 -> Some (UniversalElimination (t1, p1))
                      | None -> None)
                   | None -> None))
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ ->
                  match p with
                  | Wire_types.Number _ -> None
                  | Wire_types.Pair (a, p0) ->
                    (match fol_formula_value a with
                     | Some a0 ->
                       (match proof_value p0 with
                        | Some p1 -> Some (Explosion (a0, p1))
                        | None -> None)
                     | None -> None))
                  (fun n6 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ ->
                    match p with
                    | Wire_types.Number _ -> None
                    | Wire_types.Pair (a, b) ->
                      (match fol_formula_value a with
                       | Some a0 ->
                         (match fol_formula_value b with
                          | Some b0 -> Some (Peirce (a0, b0))
                          | None -> None)
                       | None -> None))
                    (fun _ -> None)
                    n6)
                  n5)
                n4)
              n3)
            n2)
          n1)
        n0)
   | Wire_types.Pair (_, _) -> None)

(** val certificate_code : Wire_types.code certificate -> Wire_types.code **)

let certificate_code c =
  Wire_types.Pair ((list_code (fun x -> x) c.assumptions),
    (proof_code c.deduction))

(** val certificate_value :
    Wire_types.code -> Wire_types.code certificate option **)

let certificate_value = function
| Wire_types.Number _ -> None
| Wire_types.Pair (ids, p) ->
  (match list_value (fun x -> Some x) ids with
   | Some ids0 ->
     (match proof_value p with
      | Some p0 -> Some { assumptions = ids0; deduction = p0 }
      | None -> None)
   | None -> None)

module ContextMap = ClauseMap

(** val lift : int -> form -> form **)

let lift k =
  subst (fun i -> Var ((+) k i))

(** val infer_indexed :
    (form * int) ContextMap.t -> int -> int -> proof -> form option **)

let rec infer_indexed context size depth = function
| Assume i ->
  if (&&) ((<=) 0 i) (negb ((<=) size i))
  then (match ContextMap.find
                ((fun n m -> Stdlib.max 0 (n-m)) size (Stdlib.Int.succ i))
                context with
        | Some p0 ->
          let (a, d) = p0 in
          Some (lift ((fun n m -> Stdlib.max 0 (n-m)) depth d) a)
        | None -> None)
  else None
| ImplicationIntroduction (a, p0) ->
  option_map (fun x -> Imp (a, x))
    (infer_indexed (ContextMap.add size (a, depth) context) (Stdlib.Int.succ
      size) depth p0)
| ImplicationElimination (p0, q) ->
  (match infer_indexed context size depth p0 with
   | Some f ->
     (match f with
      | Imp (a, b) ->
        (match infer_indexed context size depth q with
         | Some a' -> if form_dec a a' then Some b else None
         | None -> None)
      | _ -> None)
   | None -> None)
| UniversalIntroduction p0 ->
  option_map (fun x -> All x)
    (infer_indexed context size (Stdlib.Int.succ depth) p0)
| UniversalElimination (t0, p0) ->
  (match infer_indexed context size depth p0 with
   | Some f -> (match f with
                | All a -> Some (instantiate t0 a)
                | _ -> None)
   | None -> None)
| Explosion (a, p0) ->
  (match infer_indexed context size depth p0 with
   | Some f -> (match f with
                | Bot -> Some a
                | _ -> None)
   | None -> None)
| Peirce (a, b) -> Some (Imp ((Imp ((Imp (a, b)), a)), a))

(** val index_context : form list -> (form * int) ContextMap.t * int **)

let rec index_context = function
| [] -> (ContextMap.empty, 0)
| a :: g0 ->
  let (context, size) = index_context g0 in
  ((ContextMap.add size (a, 0) context), (Stdlib.Int.succ size))

(** val proof_size : proof -> int **)

let rec proof_size = function
| ImplicationIntroduction (_, p0) -> Stdlib.Int.succ (proof_size p0)
| ImplicationElimination (p0, q) ->
  Stdlib.Int.succ ((+) (proof_size p0) (proof_size q))
| UniversalIntroduction p0 -> Stdlib.Int.succ (proof_size p0)
| UniversalElimination (_, p0) -> Stdlib.Int.succ (proof_size p0)
| Explosion (_, p0) -> Stdlib.Int.succ (proof_size p0)
| _ -> Stdlib.Int.succ 0

(** val fast_check : ('a1 -> form option) -> 'a1 certificate -> bool **)

let fast_check axiom_at0 c =
  if (<=) (proof_size c.deduction) (Stdlib.Int.succ (Stdlib.Int.succ
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
       (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  then check axiom_at0 c
  else (match context_at axiom_at0 c.assumptions with
        | Some g ->
          let (context, size) = index_context g in
          (match infer_indexed context size 0 c.deduction with
           | Some f -> (match f with
                        | Bot -> true
                        | _ -> false)
           | None -> false)
        | None -> false)

(** val direct_check : Source_checker.theory -> Wire_types.code -> bool **)

let direct_check t0 c =
  match certificate_value c with
  | Some c0 -> fast_check (axiom_at t0) c0
  | None -> false

(** val reference_search :
    Source_checker.theory -> int -> Wire_types.code option **)

let reference_search t0 n0 =
  search decode (fun _ -> direct_check t0) n0

(** val reference_run :
    Source_checker.theory -> int -> Wire_types.code option **)

let rec reference_run t0 n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> reference_search t0 0)
    (fun n1 ->
    match reference_run t0 n1 with
    | Some c -> Some c
    | None -> reference_search t0 (Stdlib.Int.succ n1))
    n0

(** val index_bits : int -> int -> string **)

let rec index_bits fuel n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> "")
    (fun fuel0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> "")
      (fun _ ->
      (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      ((if (=) n0 (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Nat.div2 n0))
        then '0'
        else '1'),
      (index_bits fuel0 (Nat.div2 n0))))
      n0)
    fuel

(** val index_text : int -> string **)

let index_text n0 =
  index_bits n0 n0

(** val read_bits : string -> int option **)

let rec read_bits text =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> Some 0)
    (fun bit rest ->
    match read_bits rest with
    | Some n0 ->
      if (=) bit '0'
      then Some (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) n0)
      else if (=) bit '1'
           then Some (Stdlib.Int.succ
                  (mul (Stdlib.Int.succ (Stdlib.Int.succ 0)) n0))
           else None
    | None -> None)
    text

(** val index_value : string -> int option **)

let index_value text =
  match read_bits text with
  | Some n0 -> if (=) (index_text n0) text then Some n0 else None
  | None -> None

(** val enumeration_name : string **)

let enumeration_name =
  "enumerated"

(** val enumerated_check :
    (int -> formula option) -> string -> formula -> bool **)

let enumerated_check step data f =
  match index_value data with
  | Some n0 -> (match step n0 with
                | Some a -> equivalent a f
                | None -> false)
  | None -> false

type task = int list * int

(** val children : int -> int list -> int -> task list **)

let children alphabet prefix depth =
  map (fun x -> ((app prefix (x :: [])), depth)) (seq 0 alphabet)

(** val initial_jobs : int -> task list **)

let initial_jobs level0 =
  map (fun d -> ([], d)) (seq 0 (Stdlib.Int.succ level0))

type cursor = { level : int; pending : task list;
                witness : Wire_types.code option }

(** val initial_at : int -> cursor **)

let initial_at n0 =
  { level = n0; pending = (initial_jobs n0); witness = None }

(** val initial : cursor **)

let initial =
  initial_at 0

(** val tick : Source_checker.theory -> cursor -> cursor **)

let tick theory0 c =
  match c.witness with
  | Some _ -> c
  | None ->
    (match c.pending with
     | [] -> initial_at (Stdlib.Int.succ c.level)
     | t0 :: rest ->
       let (prefix, n0) = t0 in
       ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> { level = c.level; pending = rest; witness =
          (attempt decode (fun _ -> direct_check theory0) 0 prefix) })
          (fun d -> { level = c.level; pending =
          (app (children (Stdlib.Int.succ c.level) prefix d) rest); witness =
          None })
          n0))
