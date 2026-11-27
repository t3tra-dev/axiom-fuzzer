(* Wall-clock deadline for hot guard calls; see deadline.mli. *)

type t = {
  limit : int;  (** absolute monotonic nanoseconds; [max_int] = none *)
  mutable left : int;  (** checks until the next clock read *)
  mutable stride : int;
  mutable last : int;  (** nanoseconds at the last clock read *)
  mutable expired : bool;
}

let max_stride = 16

(* Stride adaptation thresholds (nanoseconds between two clock reads). *)
let dense = 50_000
let sparse = 250_000

(* 2^62 ns is about 146 years: longer budgets never expire. *)
let horizon = 4e9

let create ?(now = Telemetry.now_ns ()) seconds =
  let expired = not (seconds > 0.) in
  let limit =
    if expired then now
    else if seconds >= horizon then max_int
    else now + Float.to_int (Float.ceil (seconds *. 1e9))
  in
  { limit; left = 1; stride = 1; last = now; expired }

let read d =
  let now = Telemetry.now_ns () in
  if now >= d.limit then (
    d.expired <- true;
    true)
  else
    let gap = now - d.last in
    d.last <- now;
    if gap > sparse then d.stride <- 1
    else if gap < dense && d.stride < max_stride then d.stride <- 2 * d.stride;
    d.left <- d.stride;
    false

let expired d =
  d.expired
  ||
  (d.left <- d.left - 1;
   d.left <= 0 && read d)
[@@inline]

let expired_now d = d.expired || read d

let remaining d =
  if d.expired then 0. else Float.of_int (max 0 (d.limit - Telemetry.now_ns ())) *. 1e-9
