/* Per-Domain heap statistics for the memory budget. They read
   runtime internals, so this file defines CAML_INTERNALS; it is kept apart from
   telemetry_stubs.c, whose clock code includes the macOS mach headers, because
   with CAML_INTERNALS caml/misc.h defines macros (fallthrough, NSEC_PER_SEC, ...)
   that clash with those headers. The layout used here is the same in OCaml 5.1
   through 5.5; older runtimes report -1 (unavailable). */
#define CAML_INTERNALS
#include <caml/mlvalues.h>
#include <caml/version.h>
#if OCAML_VERSION >= 50100
#include <caml/domain_state.h>
#include <caml/gc_stats.h>
#include <caml/major_gc.h>
#include <caml/shared_heap.h>
#endif

/* Words of the calling Domain's own major heap: allocated pool blocks that the
   sweeper has not yet freed, plus large allocations. Each Domain maintains these
   counters for itself, so the reading neither includes nor waits for other
   Domains. Garbage is subtracted only when the owning Domain sweeps it. */
CAMLprim value axiom_domain_major_words(value unit) {
  (void)unit;
#if OCAML_VERSION >= 50100
  struct heap_stats s;
  caml_collect_heap_stats_sample(Caml_state->shared_heap, &s);
  return Val_long(s.pool_live_words + s.large_words);
#else
  return Val_long(-1);
#endif
}

/* Completed major GC cycles of the whole runtime. */
CAMLprim value axiom_major_cycles(value unit) {
  (void)unit;
#if OCAML_VERSION >= 50100
  return Val_long((intnat)caml_major_cycles_completed);
#else
  return Val_long(-1);
#endif
}
