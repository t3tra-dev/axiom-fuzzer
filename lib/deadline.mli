(** Wall-clock deadline for hot guard calls.

    [expired] reads the monotonic clock ([Telemetry.now_ns]) only on every [stride]-th call. The
    stride adapts to the observed call rate: it doubles (up to 16) while consecutive reads are less
    than 50 us apart and drops to 1 at the first read that is more than 250 us after the previous
    one. An expired deadline is therefore noticed at most 15 calls after the limit. The bound is in
    calls, not in time: the stride only shrinks at a read, so when calls turn sparse right after a
    dense phase, up to 15 sparse calls can pass before the next read, and the lateness can reach 15
    times the longest gap between consecutive calls. Once a read has seen the sparse gap, every
    later call reads the clock. Callers that need a bound in time call [expired_now] at coarse
    boundaries; the engine does so at the start of every step, so this lateness never carries over
    from one step to the next.

    The clock is [mach_absolute_time] on macOS, which does not advance while the system sleeps, and
    [clock_gettime(CLOCK_MONOTONIC)] elsewhere. On macOS a budget therefore counts awake time only
    ([CLOCK_MONOTONIC] there also counts sleep).

    There is no helper thread and no shared timestamp: the state is a private record that the owner
    polls, so a deadline keeps working in a [Unix.fork] child, including one created before the
    fork. Polling never allocates. A deadline is not thread-safe; every worker owns its own. *)

type t

val create : ?now:int -> float -> t
(** [create seconds] expires [seconds] after [now] (default: the current [Telemetry.now_ns]). A
    budget that is not positive (including NaN) is already expired, so the first check stops;
    budgets of 4e9 seconds or more never expire. *)

val expired : t -> bool
(** Amortized check; once true, it stays true. *)

val expired_now : t -> bool
(** Precise check: always reads the clock unless already expired. *)

val remaining : t -> float
(** Seconds left, 0 once expired (reads the clock). *)
