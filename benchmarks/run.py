"""Bounded internal benchmarks, or fixed-input comparisons with Release ATPs."""
import argparse
import csv
import datetime
import contextlib
import json
import math
import os
import pathlib
import platform
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
from external import (REPOSITORIES, Releases, SetupError, Tool, command_for, host_target,
                      native_binary, run_logged, sha256, szs_result, temporary_tools)
from corpus import applications

ROOT = pathlib.Path(__file__).resolve().parents[1]
CASES = [("naive", "UNSAT"), ("separation-universal", "UNSAT"), ("foundation-self", "UNSAT"),
         ("mutated-separation", "UNSAT"), ("separation", "UNKNOWN"), ("zf", "UNKNOWN")]
PHASES = (
    "arguments", "input_read", "input_parse", "theory_setup", "theory_copy", "history", "portfolio",
    "engine_setup", "initial_axioms", "search", "proof_extract", "proof_check", "output",
    "certificate_encode", "certificate_write", "export_fof", "export_cnf", "export_tstp",
    "export_rocq", "metrics_write", "unattributed",
)
FIELDS = [
    "case", "run", "position", "solver", "result", "szs_status", "verified",
    "expected", "domain", "problem_source",
    "wall_seconds", "budget_seconds", "timed_out", "returncode", "problem_sha256",
    "problem_bytes", "axioms", "origin", "tag", "release", "acquisition", "binary_sha256",
    "search_seconds", "replay_seconds", "generated", "retained", "proof_steps",
    "reason", "command", "log", "certificate",
    "profile", "profile_complete", "profile_active_phase", "application_seconds",
    "application_cpu_seconds", "application_allocated_words", "outside_application_seconds",
] + [f"profile_{phase}_seconds" for phase in PHASES]


def bindings(items, label):
    result = {}
    for item in items:
        name, separator, value = item.partition("=")
        if not separator or name not in REPOSITORIES or not value or name in result:
            raise ValueError(f"{label} requires a unique PROVER=VALUE: {item}")
        result[name] = value
    return result


def internal(args):
    """Keep the original six end-to-end schema-search regression benchmarks."""
    rows = []
    with tempfile.TemporaryDirectory(prefix="axiom-benchmark-") as directory:
        temp = pathlib.Path(directory)
        for theory, expected in CASES:
            for run in range(args.runs):
                stats = temp / "stats.csv"
                command = [
                    str(args.binary), "--theory", theory, "--quiet",
                    "--seconds", str(args.seconds), "--max-given", "100",
                    "--max-generated", "10000", "--metrics", str(stats),
                ]
                output = subprocess.run(command, check=True, capture_output=True, text=True,
                                        timeout=args.seconds + 20)
                with stats.open() as stream:
                    row = {"theory": theory, "run": run, **next(csv.DictReader(stream))}
                if row["result"] != expected:
                    raise RuntimeError(f"unexpected result for {theory}: {output.stdout}")
                rows.append(row)
                print(f"{theory}: {row['result']} generated={row['generated']} "
                      f"proof_steps={row['proof_steps']}", flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def corpus(args, artifacts):
    """Prepare one immutable, validated input shared by every prover."""
    result = []
    problems = artifacts / "problems"
    problems.mkdir()
    if args.problem:
        sources = [{"case": f"input-{i:03d}", "source": p} for i, p in enumerate(args.problem)]
    else:
        suite = args.suite or "schemas"
        sources = ([{"case": name, "expected": expected, "domain": "set-theory"}
                    for name, expected in CASES] if suite in ("schemas", "all") else [])
        if suite in ("applications", "all"):
            sources.extend(applications())
    if args.case:
        unknown = set(args.case) - {s["case"] for s in sources}
        if unknown:
            raise ValueError(f"unknown cases: {', '.join(sorted(unknown))}")
        sources = [s for s in sources if s["case"] in args.case]
    for entry in sources:
        name, source = entry["case"], entry.get("source")
        started = time.monotonic()
        if source is not None or "text" in entry:
            problem = problems / f"{name}.p"
            if source is None:
                problem.write_text(entry["text"])
            else:
                shutil.copyfile(source, problem)
            # Accept exactly the common FOF/CNF input language, including roles.
            # In particular, a conjecture must not be misreported as inconsistent axioms.
            validated = run_logged(
                [args.binary, "--problem", problem, "--quiet",
                 "--seconds", "0", "--max-given", "0", "--max-instances", "0"],
                problems / f"{name}-validation.log", 60,
            )
            if validated["returncode"] != 0 or validated["timed_out"]:
                raise RuntimeError(f"input is outside the supported common FOF/CNF subset: {name}; "
                                   f"see {problems / (name + '-validation.log')}")
        else:
            directory = problems / name
            command = [str(args.mutate_binary), "--theory", name, "--mutations", "0",
                       "--observations", str(args.observations), "--output-dir", str(directory)]
            run = run_logged(command, problems / f"{name}-generation.log", 60)
            if run["returncode"] != 0 or run["timed_out"]:
                raise RuntimeError(f"finite corpus generation failed: {name}")
            problem = directory / "original.p"
        data = problem.read_bytes()
        result.append({
            **{k: v for k, v in entry.items() if k not in ("text", "source", "file")},
            "case": name, "path": problem, "problem_sha256": sha256(problem),
            "problem_bytes": len(data),
            "axioms": entry.get("axioms", sum(line.startswith(b"fof(") for line in data.splitlines())
                                if source is None else ""),
            "generation_seconds": time.monotonic() - started,
        })
    return result


def read_profile(path):
    """Read cumulative completed stages; ignore a last line interrupted by SIGKILL."""
    if not path.exists():
        return {}, False, ""
    lines = path.read_text().splitlines(keepends=True)
    records, active, complete = {}, [], False
    for row in csv.DictReader(line for line in lines if line.endswith("\n")):
        name, event = row["phase"], row["event"]
        if event == "start":
            active.append(name)
        elif event in ("end", "complete", "error"):
            records[name] = row
            if active and active[-1] == name:
                active.pop()
            if name == "application":
                complete = event == "complete"
    return records, complete, active[-1] if active else ""


def measure(tool, problem, args, artifacts, run, position, env):
    stem = f"{problem['case']}-{run:03d}-{tool.name}"
    output, stats, cert, profile = [artifacts / (stem + ext)
                                   for ext in (".log", ".csv", ".cert", ".profile.csv")]
    if tool.name == "axiom-fuzzer":
        command = [
            str(tool.executable), "--problem", str(problem["path"]), "--quiet",
            "--workers", "1", "--max-instances", "0", "--seconds", str(args.seconds),
            "--max-given", "1000000", "--max-generated", "10000000",
            "--max-retained", "1000000", "--metrics", str(stats), "--certificate", str(cert),
        ]
        if args.profile:
            command.extend(["--profile", str(profile)])
    else:
        command = command_for(tool.name, tool.executable, problem["path"], args.seconds)
    try:
        completed = run_logged(command, output, args.seconds, env=env)
    except OSError as error:
        output.write_text(str(error) + "\n")
        completed = {"returncode": -1, "timed_out": False, "wall_seconds": 0.}
    row = dict.fromkeys(FIELDS, "")
    row.update(
        case=problem["case"], run=run, position=position, solver=tool.name, verified=False,
        expected=problem.get("expected", ""), domain=problem.get("domain", ""),
        problem_source=problem.get("problem_source", ""),
        wall_seconds=f"{completed['wall_seconds']:.9f}", budget_seconds=args.seconds,
        timed_out=completed["timed_out"], returncode=completed["returncode"],
        problem_sha256=problem["problem_sha256"], problem_bytes=problem["problem_bytes"],
        axioms=problem["axioms"], origin=tool.provenance.get("origin", ""),
        tag=tool.provenance.get("tag", ""),
        release=tool.provenance.get("tag", "") if tool.provenance.get("origin") == "release" else "",
        acquisition=tool.provenance["method"], binary_sha256=tool.provenance["executable_sha256"],
        command=json.dumps(command), log=str(output.relative_to(args.output.parent)),
    )
    if tool.name == "axiom-fuzzer":
        if args.profile:
            phases, complete, active = read_profile(profile)
            row.update(profile=str(profile.relative_to(args.output.parent)),
                       profile_complete=complete, profile_active_phase=active)
            for name in PHASES:
                if name in phases:
                    row[f"profile_{name}_seconds"] = phases[name]["seconds"]
            if complete:
                app = phases["application"]
                for field in ("seconds", "cpu_seconds", "allocated_words"):
                    row["application_" + field] = app[field]
                # This includes loader/runtime/module initialization, exit, and
                # parent scheduling overhead. It is not a pure startup timer.
                row["outside_application_seconds"] = (
                    f"{completed['wall_seconds'] - float(app['seconds']):.9f}")
        row["result"] = "UNKNOWN" if completed["timed_out"] else "ERROR"
        row["reason"] = "wall timeout" if completed["timed_out"] else "missing metrics or failed process"
        if completed["returncode"] == 0 and not completed["timed_out"] and stats.exists():
            with stats.open() as stream:
                measured = next(csv.DictReader(stream))
            row.update(result=measured["result"], search_seconds=measured["seconds"])
            for field in ("replay_seconds", "generated", "retained", "proof_steps", "reason"):
                row[field] = measured.get(field, "")
            if row["result"] == "UNSAT":
                if cert.is_file() and cert.stat().st_size:
                    row.update(verified=True, certificate=str(cert.relative_to(args.output.parent)))
                else:
                    row.update(result="ERROR", reason="UNSAT without saved verified certificate")
            elif row["result"] != "UNKNOWN":
                row.update(result="ERROR", reason="unexpected internal status")
    else:
        row["result"], row["szs_status"] = szs_result(
            output.read_text(errors="replace"), completed["returncode"], completed["timed_out"])
        row["reason"] = ("wall timeout" if completed["timed_out"] else
                         row["szs_status"] or "no SZS status")
    if sha256(problem["path"]) != problem["problem_sha256"]:
        raise RuntimeError("benchmark input changed during a measurement")
    return row


def comparison(args):
    names = list(REPOSITORIES) if "all" in args.external else list(dict.fromkeys(args.external))
    provided = bindings(args.external_bin, "--external-bin")
    tags = bindings(args.tag, "--tag")
    names = list(dict.fromkeys([*names, *provided]))
    if set(tags) - set(names) or set(tags) & set(provided):
        raise ValueError("--tag must name a downloaded prover")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.output.exists():
        raise ValueError(f"comparison output already exists: {args.output}; choose a new --output")
    artifacts = pathlib.Path(tempfile.mkdtemp(prefix=args.output.stem + "-", dir=args.output.parent))
    manifest_path = artifacts / "manifest.json"
    manifest = {
        "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform": platform.platform(), "target": "/".join(host_target()),
        "arguments": vars(args), "artifacts": artifacts, "status": "preparing",
        "method": "fixed finite inputs; fresh sequential processes; rotated solver order; wall deadline",
        "threads": {"axiom-fuzzer": "1 heuristic + 1 certified enumerator", "external": 1}, "external_proofs_checked": False, "tools": [], "problems": [],
    }
    print(f"Benchmark artifacts: {artifacts}", flush=True)
    rows = []
    try:
        problems = corpus(args, artifacts)
        manifest["problems"] = problems
        manifest["generator_sha256"] = (sha256(args.mutate_binary) if not args.problem and
                                       args.suite != "applications" else None)
        manifest["profile_enabled"] = args.profile
        manifest["distinct_inputs"] = len({p["problem_sha256"] for p in problems})
        with (temporary_tools(args.keep_tools) if names else contextlib.nullcontext(None)) as temporary:
            releases = Releases(temporary, artifacts / "tools", tags=tags, jobs=args.jobs,
                                setup_seconds=args.setup_seconds, source=args.source,
                                zipper_ocaml=args.zipper_ocaml) if names else None
            tools = [Tool("axiom-fuzzer", args.binary, {
                "name": "axiom-fuzzer", "method": "local", "executable": str(args.binary),
                "executable_sha256": sha256(args.binary),
            })]
            manifest["tools"].append(tools[0].provenance)
            for name in names:
                if name in provided:
                    binary = pathlib.Path(provided[name]).resolve(strict=True)
                    if not native_binary(binary, *releases.target):
                        raise SetupError(f"provided {name} binary does not match the host")
                    releases.smoke(name, binary)
                    tool = Tool(name, binary, {"name": name, "method": "provided",
                                              "executable": str(binary), "executable_sha256": sha256(binary)})
                else:
                    tool = releases.install(name)
                tools.append(tool)
                manifest["tools"].append(tool.provenance)
            manifest["status"] = "running"
            manifest_path.write_text(json.dumps(manifest, indent=2, default=str) + "\n")
            env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", LC_ALL="C")
            with args.output.open("x", newline="") as stream:
                writer = csv.DictWriter(stream, fieldnames=FIELDS)
                writer.writeheader()
                for case_index, problem in enumerate(problems):
                    for run in range(args.runs):
                        offset = (run + case_index) % len(tools)
                        for position, tool in enumerate(tools[offset:] + tools[:offset]):
                            row = measure(tool, problem, args, artifacts, run, position, env)
                            writer.writerow(row)
                            stream.flush()
                            rows.append(row)
                            print(f"{row['case']} run={run} {tool.name}: {row['result']} "
                                  f"{float(row['wall_seconds'])*1000:.3f} ms", flush=True)
            conflicts = []
            for problem in problems:
                outcomes = {r["result"] for r in rows if r["case"] == problem["case"]}
                if {"SAT", "UNSAT"} <= outcomes:
                    conflicts.append(problem["case"])
            manifest["conflicts"] = conflicts
            mismatches = sorted({r["case"] for r in rows if r["result"] in ("SAT", "UNSAT")
                                 and r["expected"] in ("SAT", "UNSAT")
                                 and r["result"] != r["expected"]})
            manifest["expected_mismatches"] = mismatches
            if conflicts or mismatches or any(r["result"] == "ERROR" for r in rows):
                raise RuntimeError("comparison contains errors, SAT/UNSAT conflicts or unexpected "
                                   "definitive results; inspect CSV and logs")
            manifest["status"] = "complete"
    except KeyboardInterrupt:
        manifest.update(status="interrupted", error="KeyboardInterrupt")
        raise
    except BaseException as error:
        manifest.update(status="failed", error=str(error))
        raise
    finally:
        manifest["measurements"] = len(rows)
        manifest_path.write_text(json.dumps(manifest, indent=2, default=str) + "\n")
    for case in dict.fromkeys(r["case"] for r in rows):
        for name in ["axiom-fuzzer", *names]:
            group = [r for r in rows if r["solver"] == name and r["case"] == case]
            outcomes = "/".join(sorted({r["result"] for r in group}))
            median = statistics.median(float(r["wall_seconds"]) for r in group) * 1000
            print(f"{case} {name}: {outcomes}, median wall {median:.3f} ms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=pathlib.Path, default=ROOT / "_build/default/bin/fuzz/main.exe")
    parser.add_argument("--mutate-binary", type=pathlib.Path, default=ROOT / "_build/default/bin/mutate/main.exe")
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--seconds", type=float, default=2.)
    parser.add_argument("--runs", type=int, default=1)
    parser.add_argument("--external", choices=[*REPOSITORIES, "all"], action="append", default=[])
    parser.add_argument("--external-bin", action="append", default=[], metavar="PROVER=PATH")
    parser.add_argument("--tag", action="append", default=[], metavar="PROVER=TAG",
                        help="pin a GitHub Release or E source tag (default: latest stable Release, E version tag)")
    parser.add_argument("--source", action="store_true", help="build all downloaded provers from Release sources")
    parser.add_argument("--keep-tools", action="store_true", help="retain the mktemp tool directory for inspection")
    parser.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    parser.add_argument("--setup-seconds", type=float, default=1800., help="setup budget per downloaded prover")
    parser.add_argument("--zipper-ocaml", default="auto",
                        help="compiler version in Zipperposition's temporary opam root (auto: solve with Release dependencies)")
    parser.add_argument("--observations", type=int, default=8, help="finite stages per schema for comparison inputs")
    parser.add_argument("--suite", choices=["schemas", "applications", "all"],
                        help="fixed inputs: six schema snapshots, eight attributed TPTP problems, or both")
    parser.add_argument("--case", action="append", default=[], metavar="NAME",
                        help="select a case by its exact name (repeatable)")
    parser.add_argument("--profile", action="store_true",
                        help="record Axiom Fuzzer pipeline wall time, CPU time and allocation")
    parser.add_argument("--problem", type=pathlib.Path, action="append", default=[],
                        help="compare on this fixed FOF/CNF input instead of the six schema snapshots")
    args = parser.parse_args()
    if (not math.isfinite(args.seconds) or args.seconds <= 0 or not math.isfinite(args.setup_seconds)
            or args.setup_seconds <= 0 or args.runs < 1 or args.jobs < 1 or args.observations < 0):
        parser.error("time/runs/jobs must be positive and finite; observations must be nonnegative")
    external = bool(args.external or args.external_bin)
    if not external and (args.tag or args.source):
        parser.error("--tag/--source require --external")
    if args.problem and args.suite:
        parser.error("--problem and --suite cannot be combined")
    fixed = external or args.problem or args.suite or args.profile or args.case
    if args.output is None:
        timestamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
        args.output = ROOT / "_build" / (f"atp-{timestamp}.csv" if fixed else "benchmarks.csv")
    args.output = args.output.resolve()
    args.binary, args.mutate_binary = args.binary.resolve(), args.mutate_binary.resolve()
    (comparison if fixed else internal)(args)
    print(args.output)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("Benchmark interrupted.", file=sys.stderr)
        sys.exit(130)
    except (SetupError, ValueError, RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(f"Benchmark failed: {error}", file=sys.stderr)
        sys.exit(2)
