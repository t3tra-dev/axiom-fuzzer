# tools

## same_search.py: does a change keep the default search?

`same_search.py` runs two `axiom-fuzz` binaries on the same bounded searches and compares what the
searches did. It is the check for changes that must not change the search: refactors, deletions of
dead code, comments, output and documentation.

### What "the same default search" means

The default search is what `axiom-fuzz` runs when no evaluation switch (`AXIOM_*`,
`--eval-strategies`) is set: the balanced portfolio for the given worker count. With one worker it
is production time-shared 1:1 with e208 on inputs without schemas, and production with the schema
probe lane on theories with schemas.

- Normal runs charge scheduling costs to the wall clock. With `AXIOM_MEASURE_COST_CLOCK=stopped`
  those costs come from a stopped clock, and a search that a cap ends (`--max-given`) depends only
  on its input and on the binary. Every comparison runs this way.
- Each strategy's engine then gives the same search in every build of a commit.
- Two parts of the default search are clocked by the binary's own allocation: the single-worker
  share (allocated words plus 20 per cooperative check, `work_clock` in
  `lib/saturation/engine.ml`) and the probe lane's default clock (`alloc_clock` in
  `lib/scheduler/probe_lane.ml`). Where their slices end depends on the compiled code, so a vanilla
  dev build and the flambda release build of one commit time-share differently. The default search
  is therefore defined per build configuration, and the two binaries compared must be built the
  same way.
- With several workers, a worker cancelled by another worker's proof stops at a timing-dependent
  point, and when two workers find proofs, the timing decides which proof is selected.

### The three levels

| Level | Runs | SAME means |
| --- | --- | --- |
| A | each of production, calc:e, e208, y1346 and sat001 alone (`--eval-strategies NAME --workers 1`) on the bundled TPTP problems and `theories/examples` | every engine searches as before; expected for any change that keeps the search, and also between build configurations |
| B | the default four-worker portfolio (`--workers 4`) on the same problems | every worker that stopped at a cap, a budget or a proof in both runs did the same; the certificate is compared when both runs selected the same worker |
| C | the default single worker (`--workers 1`) on the same problems, and the six built-in theories | the allocation-clocked slices and the probe lane are unchanged too |

Each run compares the result, the proof source, the used axioms, each heuristic worker's stop
reason, given count and memory-budget digest, the selected search's counters, the deterministic
columns of `--worker-metrics`, and the certificate bytes. A run that ends at the wall limit instead
of a cap is reported `UNSTABLE`; lower its cap in `CAPS`.

Level C is the strict one. Code motion, different inlining (for example a new `.mli` under
flambda) or a new clock can move it while levels A and B stay SAME. Such a change changes the
default search and needs its own evaluation.

### Running it

Build the base and the candidate the same way, for example the release build used for
measurements, in two checkouts:

```sh
opam exec --switch=5.5.2+flambda -- make release
```

Then compare:

```sh
python3 -I tools/same_search.py BASE/_build/default/bin/fuzz/main.exe \
  CANDIDATE/_build/default/bin/fuzz/main.exe
# One level, a subset of the runs, fewer parallel searches:
python3 -I tools/same_search.py --levels A --only 'SWV' --jobs 2 BASE CANDIDATE
# How long each run takes with the base binary (to tune CAPS):
python3 -I tools/same_search.py --calibrate BASE
```

Every line starts with `SAME`, `DIFF` or `UNSTABLE`, and a `DIFF` line is followed by the values
that differ. The exit status is 0 when every run is SAME, 1 otherwise, and 2 on a usage error. The
runs scrub every other `AXIOM_*` variable and `OCAMLRUNPARAM`, use a wall limit of 120 seconds
(`--seconds`), and keep their logs and certificates under `--out` (by default a temporary
directory, removed when every run is SAME).

There are about 100 searches per binary. With `--jobs 6` on a 14-core machine the whole comparison
takes about a minute. The reference worker would run to the wall limit, so it is stopped with
SIGINT once every heuristic worker process has exited, and it is not compared. The script needs
Python 3.9 or later and `ps` (macOS or Linux).
