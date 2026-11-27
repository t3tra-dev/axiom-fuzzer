(* Monomorphic equalities for hot search-side matching and unification.
   Polymorphic [=] on symbols and variables is a C call (compare_val) per node;
   these agree with it on every value of their types. Clausification builds
   canonical symbols and names (Intern), so equal symbols of one search are
   physically equal and the [==] tests answer them without the C string
   comparison. *)
let[@inline] string (a : string) (b : string) = a == b || String.equal a b

let equal (f : Wire.symbol) (g : Wire.symbol) =
  f == g
  ||
  match (f, g) with
  | Wire.Original a, Wire.Original b -> string a b
  | Wire.Skolem (a, b), Wire.Skolem (c, d) -> Int.equal a c && Int.equal b d
  | _ -> false
[@@inline]

let name (p : string) (q : string) = string p q [@@inline]
let def ((a, b) : int * int) ((c, d) : int * int) = Int.equal a c && Int.equal b d [@@inline]

let var ((a, b) : Wire.variable) ((c, d) : Wire.variable) = Int.equal a c && Int.equal b d
[@@inline]

(* [List.assoc_opt] specialized to variable keys. *)
let rec assoc_opt v = function
  | [] -> None
  | (k, x) :: rest -> if var k v then Some x else assoc_opt v rest
