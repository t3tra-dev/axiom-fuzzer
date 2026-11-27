"""Run the pre-registered evaluation on a split of the held-out TPTP v10.0.0 corpus.

The procedure is the one of docs/preregistration.md ("Plan for the next evaluation") and
docs/benchmarks.md: the default command line with one worker at 10 s and four workers at 30 s,
three seeds (503, 607, 701), the two arms interleaved in a seeded random order within each seed,
the whole process group killed at a hard deadline, and every UNSAT re-checked by a separate
axiom-replay against the prepared file. A case counts as solved by an arm when the majority of
its seeds gave an in-time, replayed UNSAT.

The split must be named explicitly (--split dev or --split test). Prepared files are written to
--work only; they are modified TPTP files and must not be redistributed.
"""
import argparse
import datetime
import hashlib
import json
import os
import pathlib
import platform
import random
import re
import signal
import subprocess
import sys
import threading
import time

sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "benchmarks/corpora/heldout-tptp10.json"
INCLUDE = re.compile(r"\s*include\('([^']+)'\)\.\s*")
ARMS = {"w1-10s": (1, 10.0), "w4-30s": (4, 30.0)}
SEEDS = (503, 607, 701)


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    return sha256_bytes(pathlib.Path(path).read_bytes())


def prepare(case, tptp, work):
    """Expand include lines with the complete axiom files (benchmarks/corpus.py semantics)."""
    files = {}
    for name, digest in case["source_files"].items():
        data = (tptp / name).read_bytes()
        if sha256_bytes(data) != digest:
            raise ValueError(f"{case['case']}: source checksum mismatch for {name}")
        files[name] = data.decode("utf-8")
    problem = next(n for n in case["source_files"] if n.startswith("Problems/"))

    def expand(name, stack=()):
        if name in stack or name not in files:
            raise ValueError(f"{case['case']}: unlisted or cyclic include {name}")
        out = []
        for line in files[name].splitlines(keepends=True):
            include = INCLUDE.fullmatch(line)
            if include:
                out.append(expand(include[1], (*stack, name)))
            elif re.match(r"\s*include\s*\(", line):
                raise ValueError(f"{case['case']}: unsupported include syntax in {name}")
            else:
                out.append(line)
        return "".join(out)

    data = expand(problem).encode("utf-8")
    if sha256_bytes(data) != case["prepared_sha256"] or len(data) != case["prepared_bytes"]:
        raise ValueError(f"{case['case']}: prepared file differs from the manifest")
    path = work / "prepared" / f"{case['case']}.p"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return path


def run_group(command, budget, grace, stdout_path):
    """Run a command in its own process group; kill the group at budget + grace."""
    started = time.monotonic()
    with open(stdout_path, "wb") as out:
        process = subprocess.Popen(command, stdout=out, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        deadline = started + budget + grace
        killed = False
        while True:
            pid, status, usage = os.wait4(process.pid, os.WNOHANG)
            if pid:
                break
            if time.monotonic() >= deadline:
                killed = True
                with_group(process.pid, signal.SIGKILL)
                pid, status, usage = os.wait4(process.pid, 0)
                break
            time.sleep(0.01)
        wall = time.monotonic() - started
    with_group(process.pid, signal.SIGKILL)  # reclaim anything left in the group
    process.returncode = os.waitstatus_to_exitcode(status)
    return {"returncode": process.returncode, "wall_seconds": round(wall, 4), "killed": killed,
            "cpu_seconds": round(usage.ru_utime + usage.ru_stime, 4)}


def with_group(pid, sig):
    try:
        os.killpg(pid, sig)
    except (ProcessLookupError, PermissionError):
        pass


def field(text, name):
    match = re.search(rf"^{name}: (.*)$", text, re.MULTILINE)
    return match[1].strip() if match else None


def trial(job, args, work):
    case, arm, seed = job["case"], job["arm"], job["seed"]
    workers, budget = ARMS[arm]
    stem = f"{case['case']}.{arm}.{seed}"
    cert = work / "certificates" / f"{stem}.cert"
    log = work / "logs" / f"{stem}.log"
    command = [str(args.binary), "--problem", str(job["problem"]), "--workers", str(workers),
               "--seconds", str(budget), "--quiet", "--certificate", str(cert)]
    load = os.getloadavg()[0]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    outcome = run_group(command, budget, args.grace, log)
    text = log.read_text(errors="replace")
    result = field(text, "Result") or ("KILLED" if outcome["killed"] else "ERROR")
    row = {"case": case["case"], "stratum": case["stratum"], "expected": case["expected"],
           "arm": arm, "seed": seed, "workers": workers, "budget_seconds": budget,
           "order": job["order"], "started": started, "load1": round(load, 2),
           "result": result, "reason": field(text, "Reason"), **outcome,
           "in_time": outcome["wall_seconds"] <= budget and not outcome["killed"],
           "certificate_bytes": None, "replay": None, "replay_seconds": None}
    if result == "UNSAT":
        row["certificate_bytes"] = cert.stat().st_size if cert.exists() else None
        replay_log = work / "logs" / f"{stem}.replay.log"
        replay = run_group([str(args.replay), "--problem", str(job["problem"]), str(cert)],
                           args.replay_seconds, 0, replay_log)
        replay_text = replay_log.read_text(errors="replace")
        row["replay"] = ("VERIFIED" if replay["returncode"] == 0 and "VERIFIED" in replay_text
                         else "REJECTED" if replay["returncode"] == 1 else "ERROR")
        row["replay_seconds"] = replay["wall_seconds"]
        if row["replay"] == "VERIFIED" and not args.keep_certificates:
            cert.unlink()
    row["solved"] = result == "UNSAT" and row["replay"] == "VERIFIED" and row["in_time"]
    alarms = []
    if result == "UNSAT" and case["expected"] == "SAT":
        alarms.append("FALSE_UNSAT")
    if result == "UNSAT" and row["replay"] == "REJECTED":
        alarms.append("INVALID_PROOF")
    if result == "UNSAT" and row["replay"] != "VERIFIED":
        alarms.append("UNVERIFIED_UNSAT")
    row["alarms"] = alarms
    return row


def summarize(path):
    """Print the pre-registered report of a results file (majority of seeds per case and arm)."""
    lines = [json.loads(line) for line in pathlib.Path(path).read_text().splitlines()]
    header = lines[0]["header"]
    rows = [r for r in lines[1:]]
    manifest = json.loads(MANIFEST.read_bytes())
    cases = {c["case"]: c for c in manifest["cases"] if c["split"] == header["split"]}
    print(f"Date: {header['date']}  split: {header['split']}  cases: {header['cases']}")
    print(f"Manifest sha256: {header['manifest_sha256']}")
    print(f"axiom-fuzz sha256: {header['binary_sha256']}")
    print(f"axiom-replay sha256: {header['replay_sha256']}")
    loads = sorted(r["load1"] for r in rows if "load1" in r)
    if loads:
        print(f"load1 at trial start: median {loads[len(loads) // 2]}, max {loads[-1]}")
    alarms = [r for r in rows if r.get("alarms")]
    print(f"Trials: {len(rows)}  alarms: {len(alarms)}")
    for r in alarms:
        print(f"  ALARM {r['case']} {r['arm']} {r['seed']}: {r['alarms']}")
    strata = sorted({c["stratum"] for c in cases.values() if c["expected"] == "UNSAT"})
    solved_by = {}
    for arm in ARMS:
        votes = {}
        for r in rows:
            if r.get("arm") == arm:
                votes.setdefault(r["case"], []).append(bool(r.get("solved")))
        majority = {c for c, v in votes.items() if sum(v) * 2 > len(v)}
        solved_by[arm] = majority
        unsat = [c for c in cases if cases[c]["expected"] == "UNSAT"]
        late = sum(1 for r in rows if r.get("arm") == arm and r.get("result") == "UNSAT"
                   and r.get("replay") == "VERIFIED" and not r.get("in_time"))
        some = {c for c, v in votes.items() if any(v)}
        every = {c for c, v in votes.items() if v and all(v)}
        print(f"\n{arm}: {len(majority & set(unsat))}/{len(unsat)} UNSAT cases solved "
              f"(majority of seeds); any seed {len(some & set(unsat))}, all seeds "
              f"{len(every & set(unsat))}; late replayed solves (not counted) {late}")
        for stratum in strata:
            members = [c for c in unsat if cases[c]["stratum"] == stratum]
            print(f"  {stratum}: {len(majority & set(members))}/{len(members)}")
        boundary = sorted(c for c, v in votes.items() if any(v) and not all(v))
        print(f"  boundary cases (solved by some but not all seeds): {', '.join(boundary) or '-'}")
        print(f"  solved: {', '.join(sorted(majority)) or '-'}")
    union = set().union(*solved_by.values())
    print(f"\nEither arm: {len(union)}; only w1-10s: "
          f"{', '.join(sorted(solved_by['w1-10s'] - solved_by['w4-30s'])) or '-'}; only w4-30s: "
          f"{len(solved_by['w4-30s'] - solved_by['w1-10s'])}")


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--summarize":
        summarize(sys.argv[2])
        return
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--split", choices=["dev", "test"], required=True)
    parser.add_argument("--tptp", type=pathlib.Path, required=True,
                        help="directory holding Problems/ and Axioms/ of TPTP v10.0.0")
    parser.add_argument("--binary", type=pathlib.Path, required=True, help="axiom-fuzz under test")
    parser.add_argument("--replay", type=pathlib.Path, required=True,
                        help="a separately built axiom-replay")
    parser.add_argument("--work", type=pathlib.Path, required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True, help="JSON lines, one per trial")
    parser.add_argument("--slots", type=int, default=12,
                        help="concurrent processes; a trial with N workers takes N + 1 slots")
    parser.add_argument("--grace", type=float, default=10.0)
    parser.add_argument("--replay-seconds", type=float, default=600.0)
    parser.add_argument("--keep-certificates", action="store_true")
    parser.add_argument("--case", action="append", default=[], help="restrict to these cases")
    args = parser.parse_args()

    manifest_bytes = MANIFEST.read_bytes()
    manifest = json.loads(manifest_bytes)
    cases = [c for c in manifest["cases"] if c["split"] == args.split]
    if args.case:
        cases = [c for c in cases if c["case"] in set(args.case)]
    args.work.mkdir(parents=True, exist_ok=True)
    for sub in ("certificates", "logs"):
        (args.work / sub).mkdir(exist_ok=True)
    problems = {c["case"]: prepare(c, args.tptp, args.work) for c in cases}

    jobs = []
    for seed in SEEDS:
        block = [{"case": c, "arm": arm, "seed": seed, "problem": problems[c["case"]]}
                 for c in cases for arm in ARMS]
        random.Random(seed).shuffle(block)
        jobs.extend(block)
    for order, job in enumerate(jobs):
        job["order"] = order

    header = {
        "date": datetime.date.today().isoformat(), "split": args.split,
        "manifest_sha256": sha256_bytes(manifest_bytes), "cases": len(cases),
        "binary_sha256": sha256_file(args.binary), "replay_sha256": sha256_file(args.replay),
        "arms": ARMS, "seeds": SEEDS, "slots": args.slots, "grace_seconds": args.grace,
        "machine": {"system": platform.platform(), "machine": platform.machine(),
                    "cpus": os.cpu_count()},
    }
    lock = threading.Condition()
    free = [args.slots]
    out = args.output.open("w")
    out.write(json.dumps({"header": header}) + "\n")
    out.flush()
    done = [0]

    def worker(job, weight):
        try:
            row = trial(job, args, args.work)
        except Exception as error:  # keep every row, including driver errors
            row = {"case": job["case"]["case"], "arm": job["arm"], "seed": job["seed"],
                   "result": "DRIVER_ERROR", "reason": repr(error), "solved": False,
                   "alarms": ["DRIVER_ERROR"]}
        with lock:
            out.write(json.dumps(row) + "\n")
            out.flush()
            free[0] += weight
            done[0] += 1
            if row.get("alarms"):
                print(f"ALARM {row['case']} {row['arm']} {row['seed']}: {row['alarms']}",
                      flush=True)
            if done[0] % 50 == 0:
                print(f"{done[0]}/{len(jobs)} trials", flush=True)
            lock.notify_all()

    threads = []
    for job in jobs:
        weight = ARMS[job["arm"]][0] + 1
        with lock:
            while free[0] < weight:
                lock.wait()
            free[0] -= weight
        thread = threading.Thread(target=worker, args=(job, weight))
        thread.start()
        threads.append(thread)
    for thread in threads:
        thread.join()
    out.close()
    print(f"{len(jobs)} trials written to {args.output}", flush=True)


if __name__ == "__main__":
    main()
