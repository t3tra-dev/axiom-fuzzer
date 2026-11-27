#!/usr/bin/env python3
"""lane_calibrate.py: calibrate the schema probe lane's main-engine exchange rate (main_weight, lane-clock
option (b)) so that the CLI lane wall share returns to the shares of the builds before phase 5.

Usage (stdlib only; run with python3 -I):

  python3 -I lane_calibrate.py --fuzz BIN --out DIR [--grid 1,1.6,1.8,2,2.2,2.5] [--reps 2] [--seconds 10]
      [--theories separation,zf] [--targets separation=0.49,zf=0.65] [--reference NAME=BIN ...]
      [--no-default] [--seed 503] [--weight 2] [--slots DIR] [--analyze]

What it measures
  For every (theory, repetition), every arm runs once: `BIN --theory T --seconds S --workers 1
  --quiet`, one solver at a time, each holding --weight slots of the machine-wide pool (1 worker +
  the reference Domain = 2; the pool is --slots DIR or AXF_SLOTS_DIR, a directory with slots.py;
  without any, runs are unthrottled), arms in a seeded random order
  so that load drift hits every arm alike.
  Arms: one per grid value w (environment AXIOM_LANE=main_weight=w, which replaces the build's
  default exchange rate, so the grid is absolute whatever the build's default is), the build's own
  default ("default", no AXIOM_LANE; skipped with --no-default) and any --reference build (no
  AXIOM_LANE), e.g. a build of main from before phase 5 to re-measure the targets at today's
  load. The lane wall fraction of a run is the `seconds=` of the `[lane: ...]` suffix of its Reason
  line over the process wall time: the definition of the phase-5 measurement that gave the targets
  (main before phase 5: separation 0.49-0.50, zf 0.64-0.67). Rows go to DIR/runs.jsonl (re-running the
  same command resumes: finished (theory, rep, arm, binary sha256) keys are skipped), the report to
  DIR/report.txt and DIR/report.json (--analyze only re-analyses).

The rule (two targets, one knob)
  1. Per theory t, fit logit(f) = a_t + b_t * ln(w) by least squares over the grid runs (every
     repetition is a point). Model: the lane is due while lane <= share * (lane + w * main), so at
     share 0.5 the lane allocates w times what the main engine allocates; if both sides kept a
     constant time per allocated word, the odds f / (1 - f) of the lane's wall share would be w
     times their time ratio, i.e. slope b = 1. The slopes are fitted because they are not 1 (main
     after phase 6: 0.85 on separation, 1.19 on zf; the time per word of either side drifts with how
     far it gets in the budget).
  2. Choose w* minimising the larger of the two deviations |f_t(w) - target_t| (minimax): the
     acceptance band (+-0.05 around each target) is per theory, so the worse theory decides.
     Searched in steps of 0.01 inside the measured grid range only (no extrapolation; a choice at
     the edge of the range is flagged: extend the grid). Ties go to the smaller w (less wall time
     taken from the main engine).
  3. The constant is w* rounded to 0.1 (a step of 0.1 moves a share by about 0.01); the report
     gives the fitted shares at the rounded value and the measured medians of the grid arms that
     bracket it.
  The default and reference arms are reported, never fitted.

Recalibrating on another build (same-search speed-ups change either side's allocation per unit of
search, and with it the share the allocation clock buys)
  1. Freeze the build's fuzz binary (flambda -O3, as measured) and run on a quiet slot pool:
       python3 -I lane_calibrate.py --fuzz FROZEN_FUZZ --out DIR --no-default --reference pre5=PRE5_FUZZ
     (about (grid + 1) x theories x reps runs of S + 0.05 s: 7 x 2 x 2 x 10 s, about 5 minutes).
  2. Put the reported constant into lib/scheduler/probe_lane.ml (calibrated_main_weight) and update
     the regression test that pins it (tests/regression/probe_lane_tests.ml, "the default allocation
     clock counts the main engine at the calibrated rate").
  3. Confirm on the rebuilt binary: --grid 1,CONSTANT with the default arm (no --no-default): the
     default arm must agree with the arm at the constant (same split; under
     AXIOM_MEASURE_COST_CLOCK=stopped their lane counters are identical) and both theories must be
     inside the band. If the reference build measures shares that differ from the targets by more
     than the noise (two repetitions agree within about 0.01), report it; the targets stay 0.49 /
     0.65 unless --targets says otherwise.
"""
import argparse
import hashlib
import json
import math
import os
import random
import re
import resource
import statistics
import subprocess
import sys
import time
from pathlib import Path

# Machine-wide slot pool: a directory holding slots.py with `acquire(weight)` as a context manager
# (--slots DIR or AXF_SLOTS_DIR; the bench scripts' convention, benchlib.slot_pool). Without one,
# runs are unthrottled.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from benchlib import slot_pool  # noqa: E402

LANE_SECONDS = re.compile(r"\[lane: .*?(?:^| )seconds=([0-9.]+)")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def logit(f):
    f = min(max(f, 1e-6), 1 - 1e-6)
    return math.log(f / (1 - f))


def sigmoid(x):
    return 1 / (1 + math.exp(-x))


def grab(lane, key):
    m = re.search(r"\b" + key + r"=([0-9./]+)", lane)
    return m.group(1) if m else None


def prints_stats(binary, known={}):
    """Builds that print the lane counters only with --stats list it in --help."""
    if binary not in known:
        text = subprocess.run([binary, "--help"], capture_output=True, text=True).stdout
        known[binary] = "--stats" in text
    return known[binary]


def run_one(acquire, binary, theory, seconds, env_lane, weight):
    cmd = [binary, "--theory", theory, "--seconds", str(seconds), "--workers", "1", "--quiet"]
    if prints_stats(binary):
        cmd.append("--stats")  # the Reason line's [lane: ...] counters
    env = dict(os.environ)
    env.pop("AXIOM_LANE", None)
    if env_lane:
        env["AXIOM_LANE"] = env_lane
    with acquire(weight):
        load1 = os.getloadavg()[0]
        r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
        t0 = time.time()
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env, text=True)
        out, _ = p.communicate(timeout=float(seconds) + 120)
        wall = time.time() - t0
        r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
    reason = re.search(r"^Reason: (.*)$", out, re.M)
    result = re.search(r"^Result: (\w+)", out, re.M)
    lane = reason.group(1) if reason else ""
    m = LANE_SECONDS.search(lane) or re.search(r" seconds=([0-9.]+)", lane)
    lane_seconds = float(m.group(1)) if m else None
    return {
        "result": result.group(1) if result else None,
        "code": p.returncode,
        "wall": round(wall, 3),
        "lane_seconds": lane_seconds,
        "lane_fraction": round(lane_seconds / wall, 4) if lane_seconds is not None else None,
        "turns": grab(lane, "turns"), "probes": grab(lane, "probes"), "work": grab(lane, "work"),
        "main": grab(lane, "main"), "clock_field": grab(lane, "main_weight"),
        "load1": round(load1, 2), "cpu": round(cpu, 3), "tail": None if lane_seconds is not None else out[-400:],
    }


def fit(points):
    """Least squares logit(f) = a + b ln w; with a single w the slope is the model's 1."""
    xs = [math.log(w) for w, _ in points]
    ys = [logit(f) for _, f in points]
    if len(set(round(x, 9) for x in xs)) < 2:
        b = 1.0
        a = statistics.mean(y - b * x for x, y in zip(xs, ys))
        return a, b, None
    mx, my = statistics.mean(xs), statistics.mean(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
    a = my - b * mx
    resid = [y - (a + b * x) for x, y in zip(xs, ys)]
    rmse = math.sqrt(sum(r * r for r in resid) / len(resid))
    return a, b, rmse


def analyze(rows, targets, grid_names):
    by = {}
    for r in rows:
        if r.get("lane_fraction") is None:
            continue
        by.setdefault((r["theory"], r["arm"]), []).append(r)
    report = {"targets": targets, "arms": {}, "fits": {}, "choice": None, "warnings": []}
    arms = sorted({r["arm"] for r in rows}, key=lambda a: (a not in grid_names, grid_names.get(a, 0), a))
    for t in targets:
        for a in arms:
            rs = by.get((t, a), [])
            if rs:
                fs = [r["lane_fraction"] for r in rs]
                report["arms"].setdefault(a, {})[t] = {
                    "n": len(fs), "median": round(statistics.median(fs), 4),
                    "min": min(fs), "max": max(fs),
                    "load1_median": round(statistics.median(r["load1"] for r in rs), 1),
                    "results": sorted({str(r["result"]) for r in rs}),
                }
    for t in targets:
        pts = [(grid_names[a], r["lane_fraction"]) for a in grid_names for r in by.get((t, a), [])]
        if not pts:
            report["warnings"].append(f"no grid run for {t}")
            continue
        a, b, rmse = fit(pts)
        cross = math.exp((logit(targets[t]) - a) / b) if b > 0 else None
        report["fits"][t] = {"a": round(a, 4), "b": round(b, 4), "rmse_logit": None if rmse is None else round(rmse, 4),
                             "w_at_target": None if cross is None else round(cross, 3), "points": len(pts)}
    if len(report["fits"]) < len(targets):
        return report
    ws = sorted(set(grid_names.values()))
    lo, hi = ws[0], ws[-1]
    best = None
    steps = int(round((hi - lo) / 0.01))
    for i in range(steps + 1):
        w = lo + 0.01 * i
        devs = {t: abs(sigmoid(report["fits"][t]["a"] + report["fits"][t]["b"] * math.log(w)) - targets[t])
                for t in targets}
        cost = max(devs.values())
        if best is None or cost < best[0] - 1e-12:
            best = (cost, w, devs)
    cost, w, devs = best
    rounded = round(w + 1e-9, 1)
    pred = {t: round(sigmoid(report["fits"][t]["a"] + report["fits"][t]["b"] * math.log(rounded)), 4) for t in targets}
    choice = {"w_star": round(w, 2), "max_deviation": round(cost, 4), "deviations": {t: round(d, 4) for t, d in devs.items()},
              "constant": rounded, "fitted_at_constant": pred,
              "max_deviation_at_constant": round(max(abs(pred[t] - targets[t]) for t in targets), 4),
              "in_band_0.05": all(abs(pred[t] - targets[t]) <= 0.05 for t in targets)}
    if abs(w - lo) < 0.011 or abs(w - hi) < 0.011:
        report["warnings"].append(f"w* = {w:.2f} is at the edge of the grid [{lo}, {hi}]: extend the grid")
    below = [x for x in ws if x <= rounded]
    above = [x for x in ws if x >= rounded]
    choice["bracket"] = {}
    for t in targets:
        br = {}
        for x in ([below[-1]] if below else []) + ([above[0]] if above else []):
            name = [a for a, v in grid_names.items() if v == x][0]
            cell = report["arms"].get(name, {}).get(t)
            if cell:
                br[name] = cell["median"]
        choice["bracket"][t] = br
    report["choice"] = choice
    return report


def text_report(report, meta):
    lines = [f"lanecal: {meta['fuzz']} (sha256 {meta['sha'][:12]}), {meta['seconds']} s / 1 w, "
             f"reps {meta['reps']}, targets " + ", ".join(f"{t} {v}" for t, v in report['targets'].items())]
    lines.append("")
    lines.append("arm            " + "  ".join(f"{t:>26s}" for t in report["targets"]))
    for a, cells in report["arms"].items():
        parts = []
        for t in report["targets"]:
            c = cells.get(t)
            parts.append(f"{c['median']:.3f} ({c['min']:.3f}-{c['max']:.3f}) n{c['n']} L{c['load1_median']}" if c else "-")
        lines.append(f"{a:14s} " + "  ".join(f"{p:>26s}" for p in parts))
    lines.append("")
    for t, f in report["fits"].items():
        lines.append(f"fit {t}: logit f = {f['a']:+.3f} + {f['b']:.3f} ln w (rmse {f['rmse_logit']}, {f['points']} points); "
                     f"target crossed at w = {f['w_at_target']}")
    c = report.get("choice")
    if c:
        lines.append(f"minimax w* = {c['w_star']} (max deviation {c['max_deviation']}: "
                     + ", ".join(f"{t} {d}" for t, d in c["deviations"].items()) + ")")
        lines.append(f"CONSTANT main_weight = {c['constant']}: fitted " +
                     ", ".join(f"{t} {v}" for t, v in c["fitted_at_constant"].items()) +
                     f"; max deviation {c['max_deviation_at_constant']}; in +-0.05 band: {c['in_band_0.05']}")
        lines.append("bracketing grid arms (measured medians): " +
                     "; ".join(f"{t}: " + ", ".join(f"{a} {v}" for a, v in br.items()) for t, br in c["bracket"].items()))
    for w in report["warnings"]:
        lines.append("WARNING: " + w)
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
    ap.add_argument("--fuzz", required=True, help="frozen axiom-fuzz binary of the build")
    ap.add_argument("--out", required=True)
    ap.add_argument("--grid", default="1,1.6,1.8,2,2.2,2.5")
    ap.add_argument("--reps", type=int, default=2)
    ap.add_argument("--seconds", type=float, default=10)
    ap.add_argument("--theories", default="separation,zf")
    ap.add_argument("--targets", default="separation=0.49,zf=0.65")
    ap.add_argument("--reference", action="append", default=[], help="NAME=BIN, measured without AXIOM_LANE")
    ap.add_argument("--no-default", action="store_true")
    ap.add_argument("--seed", type=int, default=503)
    ap.add_argument("--weight", type=int, default=2, help="slots per run (1 worker + the reference Domain)")
    ap.add_argument("--slots", help="directory of slots.py (default: AXF_SLOTS_DIR)")
    ap.add_argument("--analyze", action="store_true", help="only analyse DIR/runs.jsonl")
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    fuzz = os.path.realpath(args.fuzz)
    targets = dict((k, float(v)) for k, v in (x.split("=") for x in args.targets.split(",")))
    theories = args.theories.split(",")
    for t in theories:
        targets.setdefault(t, None)
    targets = {t: v for t, v in targets.items() if v is not None and t in theories}
    grid = [float(x) for x in args.grid.split(",") if x]
    grid_names = {f"w={w:g}": w for w in grid}
    sha = sha256(fuzz)
    arms = [(name, fuzz, sha, f"main_weight={w:g}") for name, w in grid_names.items()]
    if not args.no_default:
        arms.append(("default", fuzz, sha, ""))
    for spec in args.reference:
        name, _, b = spec.partition("=")
        b = os.path.realpath(b)
        arms.append((name, b, sha256(b), ""))
    runs = out / "runs.jsonl"
    rows = [json.loads(l) for l in runs.read_text().splitlines() if l.strip()] if runs.exists() else []
    done = {(r["theory"], r["rep"], r["arm"], r["sha"]) for r in rows}
    meta = {"fuzz": fuzz, "sha": sha, "seconds": args.seconds, "reps": args.reps, "grid": grid,
            "theories": theories, "targets": targets, "references": args.reference}
    if not args.analyze:
        acquire = slot_pool(args.slots)
        rng = random.Random(args.seed)
        with open(runs, "a") as f:
            for theory in theories:
                for rep in range(args.reps):
                    order = arms[:]
                    rng.shuffle(order)
                    for name, binary, bsha, lane_env in order:
                        if (theory, rep, name, bsha) in done:
                            continue
                        row = {"theory": theory, "rep": rep, "arm": name, "binary": binary, "sha": bsha,
                               "lane_env": lane_env, "seconds_budget": args.seconds}
                        row.update(run_one(acquire, binary, theory, args.seconds, lane_env, args.weight))
                        rows.append(row)
                        f.write(json.dumps(row) + "\n")
                        f.flush()
                        print(f"{theory:10s} r{rep} {name:10s} {row['result']} wall {row['wall']:.2f} "
                              f"lane {row['lane_seconds']} frac {row['lane_fraction']} load {row['load1']}",
                              flush=True)
    # Only the rows of this fuzz binary's grid enter the fit (references by name).
    rows = [r for r in rows if r["theory"] in targets and
            ((r["arm"] in grid_names or r["arm"] == "default") and r["sha"] == sha or
             r["arm"] not in grid_names and r["arm"] != "default")]
    report = analyze(rows, targets, grid_names)
    text = text_report(report, meta)
    (out / "report.txt").write_text(text + "\n")
    (out / "report.json").write_text(json.dumps({"meta": meta, **report}, indent=1))
    print(text)


if __name__ == "__main__":
    main()
