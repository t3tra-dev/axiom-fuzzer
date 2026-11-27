#!/usr/bin/env python3
"""Fixed-work identity check: does a candidate axiom-fuzz binary search exactly as a base binary?

usage: python3 -I tools/same_search.py [options] BASE CANDIDATE
       python3 -I tools/same_search.py --calibrate [options] BASE

Both binaries run the same bounded searches, and the deterministic part of each search is compared:
the result, the proof source, each heuristic worker's stop, given count and memory-budget digest, the
selected search's counters, deterministic columns of the per-worker CSV, and the certificate bytes.
See tools/README.md for what "the same default search" means and why there are three levels.

Every run uses AXIOM_MEASURE_COST_CLOCK=stopped (the scheduling costs then come from a stopped clock,
so a bounded search depends on its input and binary alone), scrubs every other AXIOM_* variable and
OCAMLRUNPARAM, and caps the search with --max-given so that it ends long before the wall limit
(--seconds, at least 120 by default). The reference worker would otherwise run to the wall limit: once
every heuristic worker process has exited, the supervisor gets SIGINT, which stops the reference
cooperatively. The heuristic workers' reports are complete by then, so this changes nothing compared.

Levels (--levels, default A,B,C):
  A  one strategy alone (--eval-strategies NAME, --workers 1) for the five strategies the default
     search can reach, on the bundled TPTP problems and the examples;
  B  the default four-worker portfolio (--workers 4); only workers stopped by a cap, a budget or a
     proof in both runs are compared, because a cancelled worker stops at a timing-dependent point,
     and the certificate only when both runs selected the same worker;
  C  the default single worker (--workers 1: production time-shared with e208 on the work clock) on
     the same problems, and the six built-in theories (production with the schema probe lane).

Exit status: 0 when every compared run is SAME, 1 when some run differs or did not reach its cap
before the wall limit (UNSTABLE: lower its cap), 2 on a usage or setup error.
"""
import argparse
import csv
import hashlib
import importlib.util
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
csv.field_size_limit(1 << 30)  # the per-worker CSV holds one JSON trace column
STRATEGIES = ("production", "calc:e", "e208", "y1346", "sat001")
THEORIES = ("naive", "separation", "separation-universal", "foundation-self", "mutated-separation",
            "zf")
EXAMPLES = ("equality", "definitions", "equality-factoring", "backward-demodulation", "satisfiable")

# --max-given caps, per input: (single strategy, four workers, default single worker). Each run must
# end at a cap, a budget or a proof long before the wall limit, also on a loaded machine; a run that
# reaches the wall limit is reported UNSTABLE, and its cap belongs lowered here. The schema theories
# run the probe lane beside the main engine and get smaller caps. --calibrate prints how long each
# run takes.
DEFAULT_CAPS = (200, 200, 200)
CAPS = {
    "SWC078-1": (120, 120, 120),
    "PLA012-1": (200, 150, 200),
    "SWV851-1": (150, 150, 150),
    "separation": (None, None, 60),
    "separation-universal": (None, None, 60),
    "mutated-separation": (None, None, 60),
    "naive": (None, None, 60),
    "zf": (None, None, 40),
    "foundation-self": (None, None, 200),
}

# Per-worker CSV columns that measure time, memory or the process rather than the search.
VOLATILE = re.compile(r"seconds|per_second|milliseconds|rss|_pid$|_exit$|_cpu|peak_domain_words|"
                      r"heap_words|allocated_words|r14_trace_json")
# Stops that a timer or another worker decided; everything else is a cap, a budget or the search.
TIMED = ("time limit", "cancelled", "memory safety limit")

HEUR = re.compile(r'^Heuristic (\d+): stop="(.*)" active_seconds=\S+ collection_seconds=\S+ '
                  r"given=(\d+) budget_responses=(\d+) cursor_drops=(\d+) trimmed=(\d+) "
                  r"peak_domain_words=\S+ peak_footprint_words=(\d+) budget_checks=(\d+) "
                  r"budget_digest=([0-9a-f]+)$", re.M)
HEUR_LOST = re.compile(r'^Heuristic (\d+): stop="(.*)"$', re.M)
METR = re.compile(r"^Metrics: generated=(\d+) retained=(\d+) given=(\d+) unifications=(\d+) "
                  r"postings=(\d+) ", re.M)


def line(text, label):
    m = re.search(r"^" + re.escape(label) + r": (.*)$", text, re.M)
    return m[1] if m else None


def problems(out):
    """The bundled TPTP problems with their includes expanded, and the examples."""
    spec = importlib.util.spec_from_file_location("corpus", ROOT / "benchmarks" / "corpus.py")
    corpus = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(corpus)
    inputs = out / "inputs"
    inputs.mkdir(parents=True, exist_ok=True)
    result = []
    for case in corpus.applications():
        path = inputs / (case["case"] + ".p")
        path.write_text(case["text"])
        result.append((case["case"], path))
    for name in EXAMPLES:
        result.append((name, ROOT / "theories" / "examples" / (name + ".p")))
    return result


def runs(levels, out):
    """(level, name, input args, worker count, strategy or None, cap) for every comparison."""
    todo = []
    tptp = problems(out)
    for name, path in tptp:
        caps = CAPS.get(name, DEFAULT_CAPS)
        if "A" in levels:
            todo += [("A", name, ["--problem", str(path)], 1, s, caps[0]) for s in STRATEGIES]
        if "B" in levels:
            todo.append(("B", name, ["--problem", str(path)], 4, None, caps[1]))
        if "C" in levels:
            todo.append(("C", name, ["--problem", str(path)], 1, None, caps[2]))
    if "C" in levels:
        todo += [("C", t, ["--theory", t], 1, None, CAPS[t][2]) for t in THEORIES]
    return todo


class Children:
    """One `ps` reading at a time, shared by every running search, of the live child processes."""

    def __init__(self):
        self.lock = threading.Lock()
        self.stamp = 0.0
        self.table = {}

    def of(self, pid):
        with self.lock:
            now = time.monotonic()
            if now - self.stamp > 0.015:
                text = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,stat="], capture_output=True,
                                      text=True).stdout
                table = {}
                for row in text.splitlines():
                    parts = row.split()
                    if len(parts) >= 3 and not parts[2].startswith("Z"):
                        table.setdefault(int(parts[1]), set()).add(int(parts[0]))
                self.table, self.stamp = table, now
            return set(self.table.get(pid, ()))


def fork_order(pids):
    """The children in the order they were forked, allowing for one wrap of the PID counter."""
    pids = sorted(pids)
    if pids and pids[-1] - pids[0] > 30000:
        cut = next(i for i in range(1, len(pids)) if pids[i] - pids[i - 1] > 30000)
        pids = pids[cut:] + pids[:cut]
    return pids


# The supervisor forks every heuristic worker and then the reference within milliseconds; after this
# long since the first child appeared, all of them exist or have already exited.
FORKED = 1.0


def search(binary, args, env, workers, seconds, log, children):
    """Runs one search; interrupts it once only the reference child (forked last) is left.

    A worker can reach its cap before the first `ps` reading sees it, so the reference is the last
    forked child seen once every fork is done. The heuristic workers have reported to the supervisor
    when they exit, so SIGINT then cancels only the reference, cooperatively."""
    with open(log, "w") as stream:
        proc = subprocess.Popen([str(binary), *args], stdout=stream, stderr=subprocess.STDOUT,
                                env=env, start_new_session=True)
        seen, interrupted, started, first = set(), False, time.monotonic(), None
        while proc.poll() is None:
            live = children.of(proc.pid)
            seen |= live
            if seen and first is None:
                first = time.monotonic()
            forked = len(seen) == workers + 1 or (
                first is not None and time.monotonic() - first > FORKED)
            if not interrupted and forked and live == {fork_order(seen)[-1]}:
                proc.send_signal(signal.SIGINT)
                interrupted = True
            if time.monotonic() - started > seconds + 120:
                os.killpg(proc.pid, signal.SIGKILL)
            time.sleep(0.02 if time.monotonic() - started < 2 else 0.1)
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    return proc.returncode, interrupted, time.monotonic() - started


def fingerprint(binary, stats, level, name, args, workers, strategy, cap, tag, a, children):
    stem = a.out / "runs" / f"{level}-{name}-{strategy or 'default'}-{tag}"
    cert, wcsv, log = (Path(str(stem) + e) for e in (".cert", ".workers.csv", ".log"))
    for p in (cert, wcsv):
        p.unlink(missing_ok=True)
    cmd = [*args, "--workers", str(workers), "--seconds", str(a.seconds), "--max-given", str(cap),
           "--quiet", "--certificate", str(cert), "--worker-metrics", str(wcsv)]
    if strategy:
        cmd += ["--eval-strategies", strategy]
    if stats:
        cmd.append("--stats")
    env = {k: v for k, v in os.environ.items()
           if not k.startswith("AXIOM_") and k != "OCAMLRUNPARAM"}
    env["AXIOM_MEASURE_COST_CLOCK"] = "stopped"
    rc, interrupted, wall = search(binary, cmd, env, workers, a.seconds, log, children)
    text = log.read_text(errors="replace")
    heur = {int(m[0]): (re.sub(r"seconds=[0-9.]+", "", m[1]), *m[2:]) for m in HEUR.findall(text)}
    for m in HEUR_LOST.findall(text):
        heur.setdefault(int(m[0]), (m[1],))
    rows = {}
    if wcsv.exists():
        for r in csv.DictReader(wcsv.open()):
            rows[int(r["worker"])] = tuple((k, re.sub(r"seconds=[0-9.]+", "", v))
                                           for k, v in r.items() if not VOLATILE.search(k))
    used = line(text, "Used axioms")
    return {
        "rc": rc,
        "result": line(text, "Result"),
        "source": line(text, "Proof source"),
        "used": used.split(", ") if used else None,
        "workers": heur,
        "rows": rows,
        "metrics": METR.findall(text),
        "cert": hashlib.sha256(cert.read_bytes()).hexdigest()[:16] if cert.exists() else "-",
        "interrupted": interrupted,
        "wall": round(wall, 2),
    }


def deterministic(worker):
    return worker is not None and not worker[0].startswith(TIMED)


def compare(level, fa, fb):
    """(verdict, differing keys): SAME, DIFF, or UNSTABLE when a run did not end at its cap."""
    keys = ["rc", "result", "used", "metrics", "source", "cert", "workers", "rows"]
    if level == "B":
        ids = [i for i in fa["workers"]
               if deterministic(fa["workers"].get(i)) and deterministic(fb["workers"].get(i))]
        a = dict(fa, workers={i: fa["workers"][i] for i in ids},
                 rows={i: fa["rows"].get(i) for i in ids})
        b = dict(fb, workers={i: fb["workers"][i] for i in ids},
                 rows={i: fb["rows"].get(i) for i in ids})
        if fa["source"] != fb["source"]:
            keys = [k for k in keys if k not in ("metrics", "source", "cert", "used")]
        diff = [k for k in keys if a[k] != b[k]]
        if not ids and not diff:
            return "UNSTABLE", ["no worker stopped deterministically in both runs"]
        return ("DIFF" if diff else "SAME"), diff
    unstable = [w for f in (fa, fb) for w in f["workers"].values() if not deterministic(w)]
    if unstable or not fa["workers"] or not fb["workers"]:
        return "UNSTABLE", [f"stop: {w[0][:60]}" for w in unstable] or ["no worker report"]
    diff = [k for k in keys if fa[k] != fb[k]]
    return ("DIFF" if diff else "SAME"), diff


def has_stats(binary):
    """Builds that moved the per-worker lines behind --stats list it in --help."""
    text = subprocess.run([str(binary), "--help"], capture_output=True, text=True).stdout
    return "--stats" in text


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("base", type=Path)
    ap.add_argument("candidate", type=Path, nargs="?")
    ap.add_argument("--levels", default="A,B,C", help="comma-separated subset of A, B and C")
    ap.add_argument("--out", type=Path, help="work directory (default: a new temporary one)")
    ap.add_argument("--jobs", type=int, default=4, help="searches run at once (default 4)")
    ap.add_argument("--seconds", type=float, default=120.0,
                    help="wall limit of every search (default 120; the caps must end it earlier)")
    ap.add_argument("--only", help="regular expression on LEVEL-NAME-STRATEGY of the runs to keep")
    ap.add_argument("--calibrate", action="store_true",
                    help="run the base binary only and print each run's stop and wall time")
    a = ap.parse_args()
    levels = {x.strip().upper() for x in a.levels.split(",") if x.strip()}
    if not levels <= {"A", "B", "C"} or (a.candidate is None) != a.calibrate:
        ap.error("give BASE and CANDIDATE (or --calibrate and BASE), and levels among A, B, C")
    binaries = [a.base] + ([] if a.calibrate else [a.candidate])
    for b in binaries:
        if not os.access(b, os.X_OK):
            ap.error(f"not an executable: {b}")
    temporary = a.out is None
    a.out = Path(tempfile.mkdtemp(prefix="same-search-")) if temporary else a.out.resolve()
    (a.out / "runs").mkdir(parents=True, exist_ok=True)
    stats = [has_stats(b) for b in binaries]
    todo = runs(levels, a.out)
    if a.only:
        todo = [r for r in todo if re.search(a.only, f"{r[0]}-{r[1]}-{r[4] or 'default'}")]
    children = Children()
    pool = ThreadPoolExecutor(max(1, a.jobs))
    jobs = [(r, [pool.submit(fingerprint, b, s, *r, tag, a, children)
                 for b, s, tag in zip(binaries, stats, "ab")]) for r in todo]
    counts = {"SAME": 0, "DIFF": 0, "UNSTABLE": 0}
    for (level, name, _, workers, strategy, cap), futures in jobs:
        fs = [f.result() for f in futures]
        label = f"{level} {name:22s} {strategy or 'default':10s} w={workers} cap={cap:<4d}"
        if a.calibrate:
            f = fs[0]
            stops = "; ".join(f"{i}:{w[0][:40]}" for i, w in sorted(f["workers"].items()))
            print(f"{label} wall={f['wall']:7.2f} int={int(f['interrupted'])} "
                  f"result={f['result']} {stops}", flush=True)
            continue
        verdict, diff = compare(level, *fs)
        counts[verdict] += 1
        print(f"{verdict:8s} {label} result={fs[0]['result']}/{fs[1]['result']} "
              f"source={fs[0]['source']}/{fs[1]['source']} cert={fs[0]['cert']}/{fs[1]['cert']} "
              f"wall={fs[0]['wall']}/{fs[1]['wall']}", flush=True)
        for k in diff:
            if k in fs[0]:
                print(f"         {k}: A={fs[0][k]}\n         {' ' * len(k)}  B={fs[1][k]}",
                      flush=True)
            else:
                print(f"         {k}", flush=True)
    pool.shutdown()
    if a.calibrate:
        return 0
    same = counts["DIFF"] == counts["UNSTABLE"] == 0
    if temporary and same:
        shutil.rmtree(a.out, ignore_errors=True)
    print(" ".join(f"{k.lower()}={v}" for k, v in counts.items())
          + (" (logs removed)" if temporary and same else f" logs={a.out}"))
    return 0 if same else 1


if __name__ == "__main__":
    sys.exit(main())
