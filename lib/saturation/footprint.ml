(* The memory budget's deterministic unit: an estimate, in words, of the search state an engine
   keeps reachable. It is computed from engine-maintained counts, never from the garbage collector,
   so it is the same under every OCAMLRUNPARAM setting, machine and load, in Domain and process
   mode and at every worker count, whenever the search itself is the same.

   [step] counts the blocks of a proof node structurally (64-bit OCaml block sizes, headers
   included, no sharing): the step record, its clause and its rule with the substitution. The
   other weights are per-object costs fitted against [Obj.reachable_words] of whole engines
   (LAT001-1 and zf, 60 s, with and without heap pressure: the fit is within 0.5x to 1.45x of the
   reachable words at every sample, and between 0.82x and 1.25x at most; checked again under the
   default budget: 0.75x to 0.94x on zf, 1.16x to 1.39x on LAT001-1). Each stored proof node
   word stands for its node, its AVATAR entry, its Passive entry and its index postings; a
   suspended Goal cursor for the posting-list versions and partner copies it pins; a Goal index
   posting for the Goal states, recipes and memo behind it. *)

let rec term = function
  | Wire.V _ -> 5
  | Wire.Fn (_, ts) -> List.fold_left (fun words t -> words + 3 + term t) 5 ts

let arguments words ts = List.fold_left (fun words t -> words + 3 + term t) words ts

let atom = function
  | Wire.P (_, ts) -> arguments 3 ts
  | Wire.E (x, y) -> 3 + term x + term y
  | Wire.D (_, ts) -> arguments 6 ts

let clause c = List.fold_left (fun words (l : Wire.literal) -> words + 6 + atom l.atom) 0 c
let substitution s = List.fold_left (fun words (_, t) -> words + 9 + term t) 0 s

let rule = function
  | Wire.Input _ -> 3
  | Wire.Component _ -> 2
  | Wire.Resolve (_, _, _, _, s) -> 6 + substitution s
  | Wire.Factor (_, _, _, s) -> 5 + substitution s
  | Wire.Equality_resolve (_, _, s) -> 4 + substitution s
  | Wire.Equality_factor (_, _, _, _, _, s) -> 7 + substitution s
  | Wire.Paramodulate (_, _, _, _, _, positions, s) ->
      8 + (3 * List.length positions) + substitution s

let step (s : Wire.step) = 4 + clause s.clause + rule s.rule

(* Weights of the fit, rounded. [stored] is a ratio [stored_numerator / stored_denominator]. *)
let stored_numerator = 9
let stored_denominator = 4
let goal_cursor = 5120
let request_cursor = 1024
let goal_posting = 256

(* Words of [stored] structural proof-node words, [goal_cursors] suspended Goal cursors,
   [request_cursors] suspended transfer request cursors and [goal_postings] Goal index postings. *)
let estimate ~stored ~goal_cursors ~request_cursors ~goal_postings =
  (stored * stored_numerator / stored_denominator)
  + (goal_cursor * goal_cursors)
  + (request_cursor * request_cursors)
  + (goal_posting * goal_postings)

(* A budget in MiB, as the CLI gives it, in footprint words (64-bit words, so the unit does not
   change with the platform). *)
let of_mib mib = mib * (1024 * 1024 / 8)
let to_mib words = words * 8 / (1024 * 1024)

(* FNV-1a over OCaml's 63-bit integers: the budget trace digest (Engine.budget_digest). *)
let mix hash x = hash lxor x * 0x100000001b3 land max_int
