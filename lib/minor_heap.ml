(* The minor heap the search processes start with.

   The runtime's default nursery is 256k words (2 MiB). The search allocates 1-5 GB/s of
   short-lived clause and term data, so a larger nursery promotes less and runs far fewer minor
   and major collections; measured on identical (stopped-clock, generated-capped) searches it saves
   cycles, not instructions. It never changes what a search does: every budget reading is a
   deterministic footprint count, and no search decision reads the collector, so the nursery is
   bounded auxiliary memory outside the footprint (its words once per process: the supervisor,
   each worker and the reference; a forked child touches its own copy as it allocates). The
   memory safety limit (Engine.safety_words) reads the major heap, which a larger nursery only
   keeps smaller.

   An explicit setting wins: when OCAMLRUNPARAM (or CAMLRUNPARAM, which the runtime reads when
   the former is unset) gives [s], nothing is changed. *)

(* 1M words (8 MiB). Measured on 46 identical capped searches (stopped clock, flambda): against the
   default 256k words, 1M saves x1.030 [1.014, 1.048] of a worker's cycles for +6 MiB per worker
   and reference process; 2M saves no more than 1M (x1.003 [0.992, 1.015] over it) for +14 MiB;
   4M saves x1.051 [1.036, 1.066] for +30 MiB. *)
let default_words = 1 lsl 20

(* Whether the runtime parameters given by the environment set the minor heap size ([s=...]). *)
let set_by_environment getenv =
  let params =
    match getenv "OCAMLRUNPARAM" with Some text -> Some text | None -> getenv "CAMLRUNPARAM"
  in
  match params with
  | None -> false
  | Some text ->
      List.exists
        (fun item -> String.length item >= 2 && item.[0] = 's' && item.[1] = '=')
        (String.split_on_char ',' text)

(* Called once at start-up, before any worker is forked or spawned. *)
let apply ?(getenv = Sys.getenv_opt) ?(words = default_words) () =
  if (not (set_by_environment getenv)) && words > (Gc.get ()).minor_heap_size then
    Gc.set { (Gc.get ()) with minor_heap_size = words }
