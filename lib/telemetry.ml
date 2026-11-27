external clock_init : unit -> unit = "axiom_clock_init"

let () = clock_init ()

(* Monotonic clock. Both readers are non-allocating C calls without locks or
   helper threads, so they keep working in a fork(2) child. *)
external now_ns : unit -> (int[@untagged]) = "axiom_monotonic_ns_byte" "axiom_monotonic_ns"
[@@noalloc]

external now : unit -> (float[@unboxed])
  = "axiom_monotonic_seconds" "axiom_monotonic_seconds_unboxed"
[@@noalloc]

(** Timings are exclusive: a nested stage pauses its caller's timer. Each worker owns its counters;
    RSS is explicitly a process-wide high water mark. *)

external peak_rss_bytes : unit -> float = "axiom_peak_rss_bytes"

external domain_major_words : unit -> int = "axiom_domain_major_words"
[@@noalloc]
(** Unswept words in the calling Domain's own major heap (pool blocks plus large allocations). Other
    Domains are not counted, and the read does not synchronize with them. Garbage leaves the count
    only after the owning Domain sweeps it. [-1] when the runtime does not provide it. *)

(* The lowest [domain_major_words] reading since [start_budget_baseline]; 0 until then. *)
let budget_baseline = Atomic.make 0
let start_budget_baseline () = Atomic.set budget_baseline (max 0 (domain_major_words ()))

(** The heuristic workers' memory-budget reading: [domain_major_words] above the baseline. A forked
    worker process inherits its supervisor's whole heap (the input, its parse and every theory copy)
    and calls [start_budget_baseline] right after the fork, so it counts only its own growth: the
    words above the lowest reading since then (a sweep of inherited garbage lowers the baseline).
    Without the call (Domains, the supervisor) the baseline stays 0 and this is
    [domain_major_words]. [-1] when the runtime does not provide it. *)
let budget_words () =
  let w = domain_major_words () in
  if w < 0 then w
  else
    let b = Atomic.get budget_baseline in
    if w >= b then w - b
    else (
      Atomic.set budget_baseline w;
      0)

external major_cycles : unit -> int = "axiom_major_cycles"
[@@noalloc]
(** Completed major collection cycles of the runtime (all Domains); [-1] if unknown. *)

type t = {
  stages : (string, float) Hashtbl.t;
  mutable current : string option;
  mutable since : float;
}

let create () = { stages = Hashtbl.create 12; current = None; since = now () }

let charge t at =
  Option.iter
    (fun name ->
      let old = Option.value ~default:0. (Hashtbl.find_opt t.stages name) in
      Hashtbl.replace t.stages name (old +. max 0. (at -. t.since)))
    t.current;
  t.since <- at

let with_stage t name f =
  let previous = t.current in
  charge t (now ());
  t.current <- Some name;
  Fun.protect f ~finally:(fun () ->
      charge t (now ());
      t.current <- previous)

let seconds t name = Option.value ~default:0. (Hashtbl.find_opt t.stages name)

let allocated_words () =
  let minor, promoted, major = Gc.counters () in
  minor +. major -. promoted
