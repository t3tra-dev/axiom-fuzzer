
val negb : bool -> bool

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val eqb : int -> int -> bool

val eqb0 : bool -> bool -> bool

module type EqLtLe =
 sig
  type t
 end

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module Nat :
 sig
  val compare : int -> int -> comparison

  val max : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool
 end

module Coq_Pos :
 sig
  val eq_dec : int -> int -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val nth_error : 'a1 list -> int -> 'a1 option

val rev : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val eqb : int -> int -> bool

  val max : int -> int -> int

  val eq_dec : int -> int -> bool
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

module OrderedTypeFacts :
 functor (O:OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> bool

  val lt_dec : O.t -> O.t -> bool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> bool

    val lt_dec : O.t -> O.t -> bool

    val eqb : O.t -> O.t -> bool
   end
 end

module Raw :
 functor (X:OrderedType) ->
 sig
  module MX :
   sig
    module TO :
     sig
      type t = X.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : X.t -> X.t -> bool

    val lt_dec : X.t -> X.t -> bool

    val eqb : X.t -> X.t -> bool
   end

  module PX :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end
   end

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

  val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

  val fold_right_pair :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

  val map2_alt :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3)
    list

  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
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

module Z_as_Int :
 sig
  type t = int

  val _0 : int

  val _1 : int

  val _2 : int

  val _3 : int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val max : int -> int -> int

  val eqb : int -> int -> bool

  val ltb : int -> int -> bool

  val leb : int -> int -> bool

  val eq_dec : int -> int -> bool

  val gt_le_dec : int -> int -> bool

  val ge_lt_dec : int -> int -> bool

  val i2z : t -> int
 end

module Coq_Raw :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2) ->
    'a1 tree -> 'a2

  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2) ->
    'a1 tree -> 'a2

  val height : 'a1 tree -> I.t

  val cardinal : 'a1 tree -> int

  val empty : 'a1 tree

  val is_empty : 'a1 tree -> bool

  val mem : X.t -> 'a1 tree -> bool

  val find : X.t -> 'a1 tree -> 'a1 option

  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min :
    'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : X.t -> 'a1 tree -> 'a1 tree

  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  val t_left : 'a1 triple -> 'a1 tree

  val t_opt : 'a1 triple -> 'a1 option

  val t_right : 'a1 triple -> 'a1 tree

  val split : X.t -> 'a1 tree -> 'a1 triple

  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

  val elements : 'a1 tree -> (key * 'a1) list

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_end : 'a1 enumeration -> bool

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) -> ('a2
    tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree

  module Proofs :
   sig
    module MX :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    module PX :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end

    module L :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      type key = X.t

      type 'elt t = (X.t * 'elt) list

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val elements : 'a1 t -> 'a1 t

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val option_cons :
        key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
        (key * 'a3) list

      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end

    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    val flatten_e : 'a1 enumeration -> (key * 'a1) list
   end
 end

module IntMake :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val height : 'a1 tree -> I.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
          -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare0

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> bool

          val lt_dec : X.t -> X.t -> bool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> bool

            val lt_dec : X.t -> X.t -> bool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
          -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Nat_as_OT :
 sig
  type t = int

  val compare : int -> int -> int compare0

  val eq_dec : int -> int -> bool
 end

module PairOrderedType :
 functor (O1:OrderedType) ->
 functor (O2:OrderedType) ->
 sig
  module MO1 :
   sig
    module TO :
     sig
      type t = O1.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O1.t -> O1.t -> bool

    val lt_dec : O1.t -> O1.t -> bool

    val eqb : O1.t -> O1.t -> bool
   end

  module MO2 :
   sig
    module TO :
     sig
      type t = O2.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O2.t -> O2.t -> bool

    val lt_dec : O2.t -> O2.t -> bool

    val eqb : O2.t -> O2.t -> bool
   end

  type t = O1.t * O2.t

  val compare : t -> t -> (O1.t * O2.t) compare0

  val eq_dec : t -> t -> bool
 end

val term_eq_dec : Rocq_checker.term -> Rocq_checker.term -> bool

val atom_eq_dec : Rocq_checker.atom -> Rocq_checker.atom -> bool

type literal = bool * Rocq_checker.atom

type clause = literal list

val term_eqb : Rocq_checker.term -> Rocq_checker.term -> bool

val atom_eqb : Rocq_checker.atom -> Rocq_checker.atom -> bool

val atom_equiv : Rocq_checker.atom -> Rocq_checker.atom -> bool

val literal_equiv : literal -> literal -> bool

val included : clause -> clause -> bool

val remove_at : int -> 'a1 list -> 'a1 list

val replace_at : int -> 'a1 -> 'a1 list -> 'a1 list

type substitution = (int * Rocq_checker.term) list

val lookup : substitution -> int -> Rocq_checker.term

val subst_term : substitution -> Rocq_checker.term -> Rocq_checker.term

val subst_atom : substitution -> Rocq_checker.atom -> Rocq_checker.atom

val subst_literal : substitution -> literal -> literal

val subst_clause : substitution -> literal list -> literal list

val fill_term :
  Rocq_checker.term_context -> Rocq_checker.term -> Rocq_checker.term

val fill_atom :
  Rocq_checker.atom_context -> Rocq_checker.term -> Rocq_checker.atom

type literal_context = bool * Rocq_checker.atom_context

val fill_literal : literal_context -> Rocq_checker.term -> literal

type step = Rocq_checker.rule * clause

type certificate = step list

module ClauseMap :
 sig
  module E :
   sig
    type t = int

    val compare : int -> int -> int compare0

    val eq_dec : int -> int -> bool
   end

  module Raw :
   sig
    type key = int

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : int -> 'a1 tree -> bool

    val find : int -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : int -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : int -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> int -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = int
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : int -> int -> bool

        val lt_dec : int -> int -> bool

        val eqb : int -> int -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = int
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : int -> int -> bool

          val lt_dec : int -> int -> bool

          val eqb : int -> int -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = int
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : int -> int -> bool

          val lt_dec : int -> int -> bool

          val eqb : int -> int -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = int
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : int -> int -> bool

            val lt_dec : int -> int -> bool

            val eqb : int -> int -> bool
           end
         end

        type key = int

        type 'elt t = (int * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
          -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = int

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

val substitution_index : substitution -> Rocq_checker.term ClauseMap.t

val indexed_lookup :
  Rocq_checker.term ClauseMap.t -> ClauseMap.key -> Rocq_checker.term

val subst_term_with :
  (int -> Rocq_checker.term) -> Rocq_checker.term -> Rocq_checker.term

val subst_atom_with :
  (int -> Rocq_checker.term) -> Rocq_checker.atom -> Rocq_checker.atom

val fast_subst_clause : substitution -> clause -> clause

val infer_with :
  (int -> clause option) -> (int -> clause option) -> Rocq_checker.rule ->
  clause option

val index_from : 'a1 list -> ClauseMap.key -> 'a1 ClauseMap.t

val cached : 'a1 list -> int -> 'a1 option

val empty_clause : clause -> bool

val replay_indexed :
  (int -> clause option) -> clause ClauseMap.t -> ClauseMap.key -> bool ->
  (Rocq_checker.rule * clause) list -> bool

val check : clause list -> (Rocq_checker.rule * clause) list -> bool

type fo_step = Avatar_checker.fo_rule * clause

type sat_literal = bool * int

type sat_clause = sat_literal list

type sat_step = Avatar_checker.sat_rule * sat_clause



module Sort :
 functor (X:TotalLeBool') ->
 sig
  val merge : X.t list -> X.t list -> X.t list

  val merge_list_to_stack :
    X.t list option list -> X.t list -> X.t list option list

  val merge_stack : X.t list option list -> X.t list

  val iter_merge : X.t list option list -> X.t list -> X.t list

  val sort : X.t list -> X.t list

  val flatten_stack : X.t list option list -> X.t list
 end

val term_scoped : int -> bool -> 'a1 Wire_types.source_term -> bool

val formula_scoped :
  int -> bool -> ('a1, 'a2) Wire_types.source_formula -> bool

val bind_term :
  int -> int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term

val bind_formula :
  int -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val lift_term :
  int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term

val substitute_term :
  int -> int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term ->
  'a1 Wire_types.source_term

val substitute_formula :
  int -> int -> 'a1 Wire_types.source_term -> ('a1, 'a2)
  Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula

module HandleOrder :
 sig
  type t = int

  val leb : int -> int -> bool
 end

module HandleSort :
 sig
  val merge : int list -> int list -> int list

  val merge_list_to_stack :
    int list option list -> int list -> int list option list

  val merge_stack : int list option list -> int list

  val iter_merge : int list option list -> int list -> int list

  val sort : int list -> int list

  val flatten_stack : int list option list -> int list
 end

val unique_after : int -> int list -> int list

val unique_sorted : int list -> int list

val sort_handles : int list -> int list

type schema_kind =
| Comprehension
| Separation
| Replacement
| UnrestrictedSeparation

val schema_arity : schema_kind -> int

val term_parameters_below : int -> 'a1 Wire_types.source_term -> bool

val parameters_below : int -> ('a1, 'a2) Wire_types.source_formula -> bool

val implication :
  ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula
  -> ('a1, 'a2) Wire_types.source_formula

val equivalence :
  ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula
  -> ('a1, 'a2) Wire_types.source_formula

val all_free :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val ex_free :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val close_parameters :
  int list -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val replacement_unique :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val replacement_functional :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val replacement_image :
  'a2 -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val schema_core :
  schema_kind -> 'a2 -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1,
  'a2) Wire_types.source_formula

val expand_schema :
  schema_kind -> 'a2 -> int list -> int -> ('a1, 'a2)
  Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula

val checked_schema :
  schema_kind -> 'a2 -> int list -> int -> ('a1, 'a2)
  Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula option

type ('f, 'p) normal =
| NPred of bool * 'p * 'f Wire_types.source_term list
| NEqual of bool * 'f Wire_types.source_term * 'f Wire_types.source_term
| NConj of ('f, 'p) normal list
| NDisj of ('f, 'p) normal list
| NAll of ('f, 'p) normal
| NEx of ('f, 'p) normal

val nnf : bool -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2) normal

val distribute : 'a1 list list -> 'a1 list list -> 'a1 list list

val product_fits : int -> int -> int -> bool

val bounded_distribute :
  int -> 'a1 list list -> 'a1 list list -> 'a1 list list option

val bounded_identity : int -> 'a1 list list -> 'a1 list list option

val bounded_cnf :
  (unit -> bool) -> int -> 'a1 Source_checker.matrix -> 'a1 list list option

val opposite :
  'a1 Source_checker.definition_literal -> 'a1
  Source_checker.definition_literal

val definition_root :
  int -> 'a1 Source_checker.definition -> 'a1
  Source_checker.definition_literal

val definition_clauses :
  int -> 'a1 Source_checker.definition -> 'a1
  Source_checker.definition_literal list list

val literal_variables :
  ('a1 -> int list) -> 'a1 Source_checker.definition_literal -> int list

val literal_before : int -> 'a1 Source_checker.definition_literal -> bool

val definition_valid :
  ('a1 -> int list) -> int -> 'a1 Source_checker.definition -> bool

val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val valid_prefix :
  (int -> 'a1 Source_checker.definition option) -> ('a1 -> int list) -> int ->
  bool

val match_connective :
  (int -> 'a1 Source_checker.definition option) -> bool -> ('a1
  Source_checker.definition_literal list -> bool) -> int -> 'a1
  Source_checker.definition_literal -> bool

val matches_matrix :
  (int -> 'a1 Source_checker.definition option) -> ('a1 -> 'a1 -> bool) -> int
  -> (bool * 'a1) Source_checker.matrix -> 'a1
  Source_checker.definition_literal -> bool

val emit_definitions :
  (int -> 'a1 Source_checker.definition option) -> (unit -> bool) -> int ->
  int -> int -> 'a1 Source_checker.definition_literal list list option

val checked_definitions :
  (int -> 'a1 Source_checker.definition option) -> (unit -> bool) -> ('a1 ->
  'a1 -> bool) -> ('a1 -> int list) -> int -> int -> (bool * 'a1)
  Source_checker.matrix -> 'a1 Source_checker.definition_literal -> 'a1
  Source_checker.definition_literal list list option

val map_option0 : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val instantiate_bound :
  (unit -> bool) -> ('a1 -> 'a2 list -> 'a2) -> 'a2 list -> 'a1
  Wire_types.source_term -> 'a2 option

type 'l universal =
| ULiteral of 'l
| UConj of 'l universal list
| UDisj of 'l universal list
| UAll of int * 'l universal

val scope_list : (int -> 'a1 -> int option) -> int -> 'a1 list -> int option

val erase_universals : 'a1 universal -> 'a1 Source_checker.matrix

type 'x supplied = { supplied_value : 'x; next_variable : int;
                     next_symbol : int }

val supply : 'a1 -> int -> int -> 'a1 supplied

val map_supply :
  (int -> int -> 'a1 -> 'a2 supplied option) -> int -> int -> 'a1 list -> 'a2
  list supplied option

val eliminate_quantifiers :
  (unit -> bool) -> ('a1 -> 'a3 list -> 'a3) -> (int -> 'a3) -> (int -> 'a3
  list -> 'a3) -> (bool -> 'a2 -> 'a3 list -> 'a4) -> (bool -> 'a3 -> 'a3 ->
  'a4) -> int -> 'a3 list -> 'a3 list -> int -> int -> ('a1, 'a2) normal ->
  'a4 universal supplied option

val term_variables : 'a1 Source_checker.wire_term -> (int * int) list

val atom_variables : ('a1, 'a2) Source_checker.wire_atom -> (int * int) list

val term_indices_acc : 'a1 Source_checker.wire_term -> int list -> int list

val atom_indices_acc : ('a1, 'a2) Source_checker.wire_atom -> int list

val wire_support : ('a1, 'a2) Source_checker.wire_atom -> int list

val local_variable : (int * int) -> bool

val wire_term_local : 'a1 Source_checker.wire_term -> bool

val wire_base_valid : ('a1, 'a2) Source_checker.wire_atom -> bool

val checked_wire_support :
  ('a1, 'a2) Source_checker.wire_atom -> int list option

type ('f, 'pT) wire_clause = ('f, 'pT) Source_checker.wire_literal list

val clause_variables : ('a1, 'a2) wire_clause -> (int * int) list

val rename_term :
  ((int * int) -> int * int) -> 'a1 Source_checker.wire_term -> 'a1
  Source_checker.wire_term

val rename_atom :
  ((int * int) -> int * int) -> ('a1, 'a2) Source_checker.wire_atom -> ('a1,
  'a2) Source_checker.wire_atom

val rename_literal :
  ((int * int) -> int * int) -> ('a1, 'a2) Source_checker.wire_literal ->
  ('a1, 'a2) Source_checker.wire_literal

val rename_clause :
  ((int * int) -> int * int) -> ('a1, 'a2) wire_clause -> ('a1, 'a2)
  Source_checker.wire_literal list

val wire_quantifiers :
  (unit -> bool) -> int -> int -> ('a1, 'a2) normal -> (bool * ('a1, 'a2)
  Source_checker.wire_atom) universal supplied option

val wire_universal_scope :
  (unit -> bool) -> int list -> int -> int -> (bool * ('a1, 'a2)
  Source_checker.wire_atom) universal -> int option

val wire_checked_universals :
  (unit -> bool) -> int -> (bool * ('a1, 'a2) Source_checker.wire_atom)
  universal -> (bool * ('a1, 'a2) Source_checker.wire_atom)
  Source_checker.matrix option

val pack_literal :
  (bool * ('a1, 'a2) Source_checker.wire_atom) -> ('a1, 'a2)
  Source_checker.wire_literal

val wire_distributive_cnf :
  (unit -> bool) -> int -> (bool * ('a1, 'a2) Source_checker.wire_atom)
  Source_checker.matrix -> ('a1, 'a2) Source_checker.wire_literal list list
  option

val wire_definition_valid :
  ('a1, 'a2) Source_checker.wire_atom Source_checker.definition_literal ->
  bool

val wire_lookup :
  (int -> ('a1, 'a2) Source_checker.wire_atom Source_checker.definition
  option) -> int -> ('a1, 'a2) Source_checker.wire_atom
  Source_checker.definition option

val wire_definitions_valid :
  (int -> ('a1, 'a2) Source_checker.wire_atom Source_checker.definition
  option) -> int -> bool

val pack_definition :
  int -> ('a1, 'a2) Source_checker.wire_atom Source_checker.definition_literal
  -> ('a1, 'a2) Source_checker.wire_literal

val wire_definitional_cnf :
  (int -> ('a1, 'a2) Source_checker.wire_atom Source_checker.definition
  option) -> (unit -> bool) -> (('a1, 'a2) Source_checker.wire_atom -> ('a1,
  'a2) Source_checker.wire_atom -> bool) -> int -> int -> int -> (bool * ('a1,
  'a2) Source_checker.wire_atom) Source_checker.matrix -> ('a1, 'a2)
  Source_checker.wire_atom Source_checker.definition_literal -> ('a1, 'a2)
  Source_checker.wire_literal list list option

val variable_equal : (int * int) -> (int * int) -> bool

val first_variables_acc :
  (int * int) list -> (int * int) list -> (int * int) list

val first_variables : (int * int) list -> (int * int) list

val variable_index : (int * int) -> (int * int) list -> int option

val local_name : (int * int) list -> (int * int) -> int * int

module VariableOrder :
 sig
  module MO1 :
   sig
    module TO :
     sig
      type t = int
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : int -> int -> bool

    val lt_dec : int -> int -> bool

    val eqb : int -> int -> bool
   end

  module MO2 :
   sig
    module TO :
     sig
      type t = int
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : int -> int -> bool

    val lt_dec : int -> int -> bool

    val eqb : int -> int -> bool
   end

  type t = int * int

  val compare : t -> t -> (int * int) compare0

  val eq_dec : t -> t -> bool
 end

module VariableMap :
 sig
  module E :
   sig
    type t = int * int

    val compare : (int * int) -> (int * int) -> (int * int) compare0

    val eq_dec : (int * int) -> (int * int) -> bool
   end

  module Raw :
   sig
    type key = int * int

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> int

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : (int * int) -> 'a1 tree -> bool

    val find : (int * int) -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : (int * int) -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : (int * int) -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> (int * int) -> 'a1 -> ('a1 enumeration -> bool)
      -> 'a1 enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = int * int
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : (int * int) -> (int * int) -> bool

        val lt_dec : (int * int) -> (int * int) -> bool

        val eqb : (int * int) -> (int * int) -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = int * int
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : (int * int) -> (int * int) -> bool

          val lt_dec : (int * int) -> (int * int) -> bool

          val eqb : (int * int) -> (int * int) -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = int * int
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : (int * int) -> (int * int) -> bool

          val lt_dec : (int * int) -> (int * int) -> bool

          val eqb : (int * int) -> (int * int) -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = int * int
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : (int * int) -> (int * int) -> bool

            val lt_dec : (int * int) -> (int * int) -> bool

            val eqb : (int * int) -> (int * int) -> bool
           end
         end

        type key = int * int

        type 'elt t = ((int * int) * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
          -> 'a3 option
       end

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = int * int

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

val collect_variables :
  VariableMap.key list -> unit VariableMap.t -> VariableMap.key list ->
  VariableMap.key list

val collected_variables : VariableMap.key list -> VariableMap.key list

val index_variables : VariableMap.key list -> int -> int VariableMap.t

val indexed_name : int VariableMap.t -> VariableMap.key -> int * int

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

module WireNormalize :
 functor (Order:WireOrder) ->
 sig
  module LiteralOrder :
   sig
    type t =
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal

    val leb :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal -> bool
   end

  module LiteralSort :
   sig
    val merge :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list

    val merge_list_to_stack :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list option list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list option list

    val merge_stack :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list option list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val iter_merge :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list option list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list

    val sort :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val flatten_stack :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list option list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list
   end

  val unique_after :
    (Order.function_name, Order.predicate_name) Source_checker.wire_literal ->
    (Order.function_name, Order.predicate_name) Source_checker.wire_literal
    list -> (Order.function_name, Order.predicate_name)
    Source_checker.wire_literal list

  val unique_sorted :
    (Order.function_name, Order.predicate_name) Source_checker.wire_literal
    list -> (Order.function_name, Order.predicate_name)
    Source_checker.wire_literal list

  val sort_clause :
    (Order.function_name, Order.predicate_name) Source_checker.wire_literal
    list -> (Order.function_name, Order.predicate_name)
    Source_checker.wire_literal list

  val normalize :
    int -> (Order.function_name, Order.predicate_name)
    Source_checker.wire_literal list -> (Order.function_name,
    Order.predicate_name) Source_checker.wire_literal list option
 end

val symbol_equal :
  ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_symbol -> 'a1
  Source_checker.wire_symbol -> bool

val predicate_equal :
  ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_predicate -> 'a1
  Source_checker.wire_predicate -> bool

val encoded_term :
  ('a1 -> 'a1 -> bool) -> ((int * int) -> int) -> (int -> 'a1
  Source_checker.wire_symbol option) -> 'a1 Source_checker.wire_term ->
  Rocq_checker.term -> bool

val encoded_predicate :
  ('a1 -> 'a1 -> bool) -> (int -> 'a1 Source_checker.wire_predicate option) ->
  'a1 Source_checker.wire_predicate -> int -> bool

val encoded_atom :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2) Source_checker.wire_atom
  -> Rocq_checker.atom -> bool

val encoded_literal :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2)
  Source_checker.wire_literal -> literal -> bool

val encoded_clause :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2)
  Source_checker.wire_literal list -> literal list -> bool

val encoded_inputs :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2)
  Source_checker.wire_literal list list -> literal list list -> bool

module WireRefutation :
 functor (Order:WireOrder) ->
 sig
  module Normalize :
   sig
    module LiteralOrder :
     sig
      type t =
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal

      val leb :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal -> bool
     end

    module LiteralSort :
     sig
      val merge :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val merge_list_to_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list

      val merge_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val iter_merge :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val sort :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val flatten_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list
     end

    val unique_after :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list

    val unique_sorted :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val sort_clause :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val normalize :
      int -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list option
   end
 end

type ('f, 'pT) source_input = { source_id : int;
                                source_text : ('f, 'pT)
                                              Wire_types.source_formula;
                                source_matrix : (bool * ('f, 'pT)
                                                Source_checker.wire_atom)
                                                Source_checker.matrix;
                                source_clauses : ('f, 'pT) wire_clause list }

module SourceRefutation :
 functor (Order:WireOrder) ->
 sig
  module Refutation :
   sig
    module Normalize :
     sig
      module LiteralOrder :
       sig
        type t =
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal

        val leb :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal -> bool
       end

      module LiteralSort :
       sig
        val merge :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list

        val merge_list_to_stack :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list option list

        val merge_stack :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list

        val iter_merge :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list

        val sort :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list

        val flatten_stack :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list
       end

      val unique_after :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val unique_sorted :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val sort_clause :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val normalize :
        int -> (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list option
     end
   end

  module Normalize :
   sig
    module LiteralOrder :
     sig
      type t =
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal

      val leb :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal -> bool
     end

    module LiteralSort :
     sig
      val merge :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val merge_list_to_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list

      val merge_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val iter_merge :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val sort :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val flatten_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list
     end

    val unique_after :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list

    val unique_sorted :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val sort_clause :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val normalize :
      int -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list option
   end
 end

type formula = (string, string) Wire_types.source_formula

type term0 = string Wire_types.source_term

val term_equal : term0 -> term0 -> bool

val formula_equal : formula -> formula -> bool

val deduplicate : formula list -> formula list

val and_parts : formula -> formula list

val or_parts : formula -> formula list

val is_bottom : formula -> bool

val is_top : formula -> bool

val smart_and : formula list -> (string, string) Wire_types.source_formula

val smart_or : formula list -> (string, string) Wire_types.source_formula

val smart_not : formula -> (string, string) Wire_types.source_formula

val simplify : formula -> formula

val formula_identical : formula -> formula -> bool

val equivalent : formula -> formula -> bool

val symbol_present : (string * int) list -> string -> int -> bool

val term_signature : (string * int) list -> term0 -> bool

val formula_signature :
  (string * int) list -> (string * int) list -> formula -> bool

val term_parameters : term0 -> int list

val formula_parameters : formula -> int list

val builtin : Wire_types.schema -> schema_kind option

val schema_equal : Wire_types.schema -> Wire_types.schema -> bool

val admitted : Wire_types.schema list -> Wire_types.schema -> bool

val signature_ok : Source_checker.theory -> formula -> bool

val fixed_origin_equal : Wire_types.origin -> Wire_types.origin -> bool

val schema_expansion :
  int -> schema_kind -> formula -> (string, string) Wire_types.source_formula
  option

val validate_axiom : int -> Source_checker.theory -> Wire_types.axiom -> bool

val wire_term_equal :
  string Source_checker.wire_term -> string Source_checker.wire_term -> bool

val wire_atom_equal :
  (string, string) Source_checker.wire_atom -> (string, string)
  Source_checker.wire_atom -> bool

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

val compile_input :
  (unit -> bool) -> int -> int -> prepared_axiom -> (string, string)
  source_input option

val compile_inputs :
  (unit -> bool) -> int -> int -> prepared_axiom list -> (string, string)
  source_input list option

val unique_from : unit ClauseMap.t -> ClauseMap.key list -> bool

val fast_unique_ids : ClauseMap.key list -> bool

module Kernel :
 functor (Order:WireOrder with type function_name = string with type predicate_name = 
 string) ->
 sig
  module Sound :
   sig
    module Refutation :
     sig
      module Normalize :
       sig
        module LiteralOrder :
         sig
          type t =
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal

          val leb :
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal -> (Order.function_name,
            Order.predicate_name) Source_checker.wire_literal -> bool
         end

        module LiteralSort :
         sig
          val merge :
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list -> (Order.function_name,
            Order.predicate_name) Source_checker.wire_literal list ->
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list

          val merge_list_to_stack :
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list option list ->
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list -> (Order.function_name,
            Order.predicate_name) Source_checker.wire_literal list option list

          val merge_stack :
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list option list ->
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list

          val iter_merge :
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list option list ->
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list -> (Order.function_name,
            Order.predicate_name) Source_checker.wire_literal list

          val sort :
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list -> (Order.function_name,
            Order.predicate_name) Source_checker.wire_literal list

          val flatten_stack :
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list option list ->
            (Order.function_name, Order.predicate_name)
            Source_checker.wire_literal list
         end

        val unique_after :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list

        val unique_sorted :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list

        val sort_clause :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list

        val normalize :
          int -> (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list option
       end
     end

    module Normalize :
     sig
      module LiteralOrder :
       sig
        type t =
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal

        val leb :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal -> bool
       end

      module LiteralSort :
       sig
        val merge :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list

        val merge_list_to_stack :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list option list

        val merge_stack :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list

        val iter_merge :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list

        val sort :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list -> (Order.function_name,
          Order.predicate_name) Source_checker.wire_literal list

        val flatten_stack :
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list option list ->
          (Order.function_name, Order.predicate_name)
          Source_checker.wire_literal list
       end

      val unique_after :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val unique_sorted :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val sort_clause :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val normalize :
        int -> (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list option
     end
   end

  module Normalize :
   sig
    module LiteralOrder :
     sig
      type t =
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal

      val leb :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal -> bool
     end

    module LiteralSort :
     sig
      val merge :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val merge_list_to_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list

      val merge_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val iter_merge :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list ->
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list

      val sort :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list

      val flatten_stack :
        (Order.function_name, Order.predicate_name)
        Source_checker.wire_literal list option list -> (Order.function_name,
        Order.predicate_name) Source_checker.wire_literal list
     end

    val unique_after :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list

    val unique_sorted :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val sort_clause :
      (Order.function_name, Order.predicate_name) Source_checker.wire_literal
      list -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list

    val normalize :
      int -> (Order.function_name, Order.predicate_name)
      Source_checker.wire_literal list -> (Order.function_name,
      Order.predicate_name) Source_checker.wire_literal list option
   end

  val normalize_inputs :
    int -> (Order.function_name, Order.predicate_name)
    Source_checker.wire_literal list list -> (Order.function_name,
    Order.predicate_name) Source_checker.wire_literal list list option

  val check_sources :
    (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
    Source_checker.wire_symbol option) -> (int -> string
    Source_checker.wire_predicate option) -> certificate1 -> bool

  val check :
    (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
    Source_checker.wire_symbol option) -> (int -> string
    Source_checker.wire_predicate option) -> Source_checker.theory ->
    certificate1 -> bool

  val avatar_check_sources :
    (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
    Source_checker.wire_symbol option) -> (int -> string
    Source_checker.wire_predicate option) -> certificate1 ->
    Avatar_checker.certificate -> bool

  val avatar_check :
    (unit -> bool) -> int -> int -> ((int * int) -> int) -> (int -> string
    Source_checker.wire_symbol option) -> (int -> string
    Source_checker.wire_predicate option) -> Source_checker.theory ->
    certificate1 -> Avatar_checker.certificate -> bool
 end
