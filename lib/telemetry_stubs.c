#include <stdint.h>
#include <time.h>
#include <sys/resource.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/fail.h>

#ifdef __APPLE__
#include <mach/mach_time.h>
#endif

/* Monotonic clock in nanoseconds. Reads are non-allocating and thread-free:
   no helper thread, no shared timestamp, nothing that a fork(2) child could
   lose. On macOS clock_gettime(CLOCK_MONOTONIC) goes through
   _mach_boottime_usec and gettimeofday; mach_absolute_time is a commpage read.
   Both are monotonic and are used only for process-relative intervals.

   The macOS timebase is packed as (numer << 32) | denom into one atomic word,
   so concurrent first readers cannot observe a torn pair. axiom_clock_init
   fills it eagerly from Telemetry's module initializer and checks that the
   clock works; a reader that runs first fills it itself. */
#ifdef __APPLE__
#include <stdatomic.h>
static _Atomic uint64_t axiom_timebase = 0;

static uint64_t axiom_load_timebase(void) {
  uint64_t tb = atomic_load_explicit(&axiom_timebase, memory_order_relaxed);
  if (tb == 0) {
    mach_timebase_info_data_t info;
    if (mach_timebase_info(&info) == 0 && info.numer != 0 && info.denom != 0)
      tb = ((uint64_t)info.numer << 32) | (uint64_t)info.denom;
    else
      tb = ((uint64_t)1 << 32) | 1; /* unreachable in practice: nanosecond ticks */
    atomic_store_explicit(&axiom_timebase, tb, memory_order_relaxed);
  }
  return tb;
}
#endif

CAMLprim value axiom_clock_init(value unit) {
  (void)unit;
#ifdef __APPLE__
  mach_timebase_info_data_t info;
  if (mach_timebase_info(&info) != 0 || info.numer == 0 || info.denom == 0)
    caml_failwith("mach_timebase_info failed");
  (void)axiom_load_timebase();
#else
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
    caml_failwith("clock_gettime(CLOCK_MONOTONIC) failed");
#endif
  return Val_unit;
}

intnat axiom_monotonic_ns(value unit) {
  (void)unit;
  /* Must not raise or allocate (noalloc external). */
#ifdef __APPLE__
  uint64_t tb = axiom_load_timebase();
  uint64_t numer = tb >> 32, denom = tb & 0xffffffffu;
  uint64_t ticks = mach_absolute_time();
  if (numer == denom) return (intnat)ticks;
  /* Split to avoid overflowing ticks * numer for long uptimes. */
  return (intnat)((ticks / denom) * numer + (ticks % denom) * numer / denom);
#else
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts); /* availability checked by axiom_clock_init */
  return (intnat)ts.tv_sec * 1000000000 + (intnat)ts.tv_nsec;
#endif
}

value axiom_monotonic_ns_byte(value unit) { return Val_long(axiom_monotonic_ns(unit)); }

double axiom_monotonic_seconds_unboxed(value unit) { return (double)axiom_monotonic_ns(unit) * 1e-9; }

CAMLprim value axiom_monotonic_seconds(value unit) {
  return caml_copy_double(axiom_monotonic_seconds_unboxed(unit));
}

CAMLprim value axiom_peak_rss_bytes(value unit) {
  struct rusage usage;
  (void)unit;
  if (getrusage(RUSAGE_SELF, &usage) != 0)
    caml_failwith("getrusage(RUSAGE_SELF) failed");
#ifdef __APPLE__
  return caml_copy_double((double)usage.ru_maxrss);
#else
  return caml_copy_double((double)usage.ru_maxrss * 1024.0);
#endif
}
