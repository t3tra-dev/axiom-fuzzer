"""CLI contracts: durable artifacts, strict replay, and non-SAT exhaustion."""
import csv
import fcntl
import os
import signal
import time
import pathlib
import subprocess
import sys
import tempfile

import clean_environment

clean_environment.scrub()
fuzz, replay, minimize, natural_fixture, mutate, fixture_root, certificate_fixture, reference = map(
    pathlib.Path, sys.argv[1:])
fuzz, replay, minimize, fixture_root, reference = (
    p.resolve() for p in (fuzz, replay, minimize, fixture_root, reference))
natural_fixture = natural_fixture.resolve()
mutate = mutate.resolve()


def run(exe, *args, code=0, env=None):
    result = subprocess.run([str(exe), *map(str, args)], capture_output=True, text=True, timeout=120,
                            env=dict(os.environ, **env) if env else None)
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    return result.stdout


def fields(out, label):
    """key=value items of a summary line such as 'Metrics:' or 'Reference:'."""
    line = next(line for line in out.splitlines() if line.startswith(label + ": "))
    return dict(item.split("=", 1) for item in line[len(label) + 2:].split() if "=" in item)


# metrics_version 6 column groups a worker computes about itself, in order (first and last
# column of each group), and the columns the process supervisor appends.
WORKER_GROUPS = [("strategy", "mix_selections", 3), ("slice_policy", "slice_main_retained", 23),
                 ("limit_given", "budget_digest", 18)]
WORKER_GROUP_WIDTH = sum(width for _, _, width in WORKER_GROUPS)
PROCESS_COLUMNS = ["worker_pid", "worker_exit", "worker_cpu_seconds", "worker_peak_rss_bytes"]
ISOLATION_COLUMNS = ["isolation", "lost_workers", "processes_cpu_seconds", "processes_peak_rss_bytes"]


def groups_follow(header, anchor, groups):
    """The groups follow column [anchor] directly, in order and without gaps."""
    at = header.index(anchor) + 1
    for first, last, width in groups:
        if header[at] != first or header[at + width - 1] != last:
            return False
        at += width
    return True


with tempfile.TemporaryDirectory(prefix="axiom-fuzzer-cli-") as temp:
    assert "VERIFIED" in run(replay, certificate_fixture.resolve())
    temp = pathlib.Path(temp)
    cert, small, rocq = temp / "proof.cert", temp / "small.cert", temp / "Proof.v"
    fof, cnf, tstp, metrics = (temp / name for name in ("axioms.p", "clauses.p", "proof.tstp", "metrics.csv"))
    out = run(fuzz, "--theory", "naive", "--quiet", "--stats", "--certificate", cert,
              "--export-fof", fof, "--export-cnf", cnf, "--tstp", tstp, "--rocq", rocq, "--metrics", metrics)
    assert "Result: UNSAT" in out and "Proof clauses: 5" in out
    # The written certificate's size, its reader limit and whether axiom-replay can read it.
    size_line = next(line for line in out.splitlines() if line.startswith("Certificate bytes: "))
    assert size_line.split()[2] == str(cert.stat().st_size), size_line
    assert fields(out, "Certificate bytes") == {"limit": str(32 * 1024 * 1024), "readable": "true"}
    assert "VERIFIED" in run(replay, cert)
    assert "VERIFIED" in run(minimize, cert, "--output", small, "--seconds", "0.2")
    assert "VERIFIED" in run(replay, small)
    run(replay, cert, "--theory", "zf", code=1)
    assert "Result: UNSAT" in run(fuzz, "--problem", fof, "--quiet")
    assert "Result: UNSAT" in run(fuzz, "--problem", cnf, "--quiet")
    assert "status(esa)" in tstp.read_text() and "new_symbols(skolem" in tstp.read_text()
    assert "source_axioms_unsatisfiable" in rocq.read_text() and "theory_refuted" in rocq.read_text()
    assert len(metrics.read_text().splitlines()) == 2
    assert "candidates" not in fields(out, "Metrics")
    workers, schemas = temp / "workers.csv", temp / "schemas.csv"
    run(fuzz, "--theory", "naive", "--quiet", "--workers", "3", "--metrics", metrics,
        "--worker-metrics", workers, "--schema-metrics", schemas)
    report = list(csv.DictReader(metrics.open()))[0]
    worker_rows = list(csv.DictReader(workers.open()))
    assert len(worker_rows) == 3
    # Version 5 worker CSV: the observation columns, the worker groups (strategy, then slices),
    # then the process columns the supervisor adds.
    worker_header = next(csv.reader(workers.open()))
    assert worker_header[308] == "r14_trace_json", worker_header[300:310]
    assert groups_follow(worker_header, "r14_trace_json", WORKER_GROUPS), worker_header[309:]
    assert worker_header[-4:] == PROCESS_COLUMNS, worker_header[-4:]
    assert len(worker_header) == 309 + WORKER_GROUP_WIDTH + 4, len(worker_header)
    # By default the balanced rule: production on the first half of the workers, then e208.
    assert [w["strategy"] for w in worker_rows] == ["production", "production", "e208"]
    assert report["strategy"] in ("production", "e208")
    assert int(report["total_generated"]) == sum(int(w["generated"]) for w in worker_rows)
    assert float(report["process_peak_rss_bytes"]) > 0
    assert all(float(w["seconds"]) <= float(report["portfolio_seconds"]) for w in worker_rows)
    schema_rows = list(csv.DictReader(schemas.open()))
    assert sum(int(s["injected"]) for s in schema_rows) == sum(int(w["injected_instances"]) for w in worker_rows)
    problem = fixture_root / "examples/definitions.p"
    assert "UNSAT" in run(fuzz, "--problem", problem, "--quiet", "--certificate", cert, "--rocq", rocq)
    assert "VERIFIED" in run(replay, cert, "--problem", problem)
    missing = temp / "must-not-exist.cert"
    out = run(fuzz, "--theory", "separation", "--seconds", "0.1", "--max-given", "5", "--quiet", "--certificate", missing)
    assert "Result: UNKNOWN" in out and not missing.exists()
    for name in ("naive-set/russell.p", "zf/separation-universal.p", "zf/foundation-self.p", "examples/equality.p"):
        problem = fixture_root / name
        assert "Result: UNSAT" in run(fuzz, "--problem", problem, "--quiet", "--certificate", cert)
        assert "VERIFIED" in run(replay, cert, "--problem", problem)
        run(replay, cert, code=2)
    assert "Result: UNKNOWN" in run(fuzz, "--problem", fixture_root / "examples/satisfiable.p", "--seconds", "0.1", "--max-given", "10", "--quiet")
    run(fuzz, "--seconds", "nan", code=2)
    # Count caps stop a worker only when given; the default memory budget trims
    # instead. Every heuristic worker reports why and when it stopped. For a schema
    # theory the reason ends with the probe lane's statistics ' [lane: ...]', so it
    # is read by prefix.
    budget_workers = temp / "budget-workers.csv"
    out = run(fuzz, "--theory", "zf", "--seconds", "0.3", "--quiet", "--stats",
              "--worker-metrics", budget_workers)
    assert 'Heuristic 0: stop="time limit [lane: ' in out and '" active_seconds=' in out, out
    assert " collection_seconds=" in out, out
    row = next(csv.DictReader(budget_workers.open()))
    assert int(row["limit_generated"]) > 2**60 and int(row["budget_heap_words"]) > 0, row
    assert int(row["budget_proof_nodes"]) > 0, row
    assert row["reason"].startswith("time limit [lane: "), row
    assert int(row["budget_responses"]) == 0, row
    # 0 disables both the heap budget and the internal proof-node budget.
    run(fuzz, "--theory", "zf", "--seconds", "0.2", "--memory-budget", "0", "--quiet",
        "--worker-metrics", budget_workers)
    row = next(csv.DictReader(budget_workers.open()))
    assert int(row["budget_heap_words"]) == 0 and int(row["budget_proof_nodes"]) == 0, row
    # The budget is per worker and fixed: the same for every worker count, in
    # 8-byte footprint words on every platform (default 256 MiB). The reference
    # reports its heap.
    out = run(fuzz, "--theory", "zf", "--seconds", "0.2", "--workers", "2", "--memory-budget", "100",
              "--quiet", "--stats", "--worker-metrics", budget_workers)
    assert "Reference heap: peak_domain_words=" in out, out
    rows = list(csv.DictReader(budget_workers.open()))
    assert [int(r["budget_heap_words"]) for r in rows] == [100 * 2**20 // 8] * 2, rows
    for count in ("1", "3"):
        run(fuzz, "--theory", "zf", "--seconds", "0.2", "--workers", count, "--quiet",
            "--worker-metrics", budget_workers)
        rows = list(csv.DictReader(budget_workers.open()))
        assert [int(r["budget_heap_words"]) for r in rows] == [256 * 2**20 // 8] * int(count), rows
        assert all(int(r["budget_checks"]) > 0 and len(r["budget_digest"]) == 16 for r in rows), rows
    out = run(fuzz, "--theory", "zf", "--seconds", "1", "--max-generated", "100", "--quiet", "--stats")
    assert 'Heuristic 0: stop="generated clause limit [lane: ' in out, out
    out = run(fuzz, "--theory", "zf", "--seconds", "0.3", "--memory-budget", "1", "--quiet",
              "--worker-metrics", budget_workers)
    row = next(csv.DictReader(budget_workers.open()))
    assert int(row["budget_heap_responses"]) >= 1 and int(row["peak_footprint_words"]) > 0, row
    assert int(row["peak_domain_words"]) > 0, row
    assert row["reason"].startswith(("time limit [lane: ", "memory budget exhausted [lane: ")), row["reason"]
    run(fuzz, "--memory-budget", "-1", code=2)
    # Backward demodulation rewrites an Active clause, keeps a portable proof
    # and exposes its counters.
    backward_problem = fixture_root / "examples/backward-demodulation.p"
    out = run(fuzz, "--problem", backward_problem, "--certificate", cert, "--metrics", metrics,
              "--rocq", rocq, "--quiet", "--stats")
    assert "Result: UNSAT" in out and "VERIFIED" in run(replay, cert, "--problem", backward_problem)
    report = next(csv.DictReader(metrics.open()))
    assert report["metrics_version"] == "6" and report["backward_demodulation"] == "true"
    assert int(report["backward_demodulated"]) >= 1
    # Version 5: after the portfolio and reference columns come the worker groups, and last the
    # process supervisor's isolation columns, as in the worker CSV.
    summary_header = next(csv.reader(metrics.open()))
    assert summary_header.index("reference_peak_domain_words") == summary_header.index("reference_reason") + 1
    assert groups_follow(summary_header, "reference_peak_domain_words", WORKER_GROUPS), summary_header[309:]
    assert summary_header[-4:] == ISOLATION_COLUMNS, summary_header[-4:]
    assert len(summary_header) == 309 + 19 + WORKER_GROUP_WIDTH + 4, len(summary_header)
    assert int(report["backward_demodulation_candidates"]) <= int(report["backward_demodulation_baseline"])
    # The stdout scan volume is the sum of the CSV posting columns of the heuristic
    # worker; this run scans both the resolution and the equality indexes.
    assert report["proof_source"].startswith("heuristic")
    resolution, equality = int(report["resolution_postings"]), int(report["equality_postings"])
    assert resolution > 0 and equality > 0
    assert int(fields(out, "Metrics")["postings"]) == resolution + equality
    # One balanced worker on an input without schemas time-shares production with e208 at queue
    # phase 0 (the share: one resumed lane, admitted at most once, on the work clock). The A/A
    # portfolio and a theory with schemas run without slices, and so does the hook's off.
    share = "[e208+0~] unit=15000000 work geometric:1 ratio=1 carry"
    assert report["slice_policy"] == share, report["slice_policy"]
    assert report["slice_probes_created"] in ("0", "1"), report["slice_probes_created"]
    for args, env in ((["--eval-strategies", "production"], {}), ([], {"AXIOM_SLICES": "off"})):
        alone = subprocess.run([str(fuzz), "--problem", str(backward_problem), "--metrics", str(metrics),
                                "--quiet", *args], capture_output=True, text=True, timeout=20,
                               env=dict(os.environ, **env))
        assert alone.returncode == 0 and "Result: UNSAT" in alone.stdout, alone
        alone_report = next(csv.DictReader(metrics.open()))
        assert alone_report["slice_policy"] == "off", (args, env, alone_report["slice_policy"])
        assert alone_report["slice_probes_created"] == "0", (args, env)
    run(fuzz, "--theory", "naive", "--seconds", "1", "--quiet", "--metrics", metrics)
    assert next(csv.DictReader(metrics.open()))["slice_policy"] == "off"
    sliced_env = dict(os.environ, AXIOM_SLICES="on")
    sliced = subprocess.run([str(fuzz), "--problem", str(backward_problem), "--certificate", str(cert),
                             "--metrics", str(metrics), "--quiet"],
                            capture_output=True, text=True, timeout=20, env=sliced_env)
    assert sliced.returncode == 0 and "Result: UNSAT" in sliced.stdout, sliced
    assert "VERIFIED" in run(replay, cert, "--problem", backward_problem)
    sliced_report = next(csv.DictReader(metrics.open()))
    assert sliced_report["slice_policy"].endswith("rounds=1"), sliced_report["slice_policy"]
    assert int(sliced_report["slice_main_given"]) >= 0
    bad = subprocess.run([str(fuzz), "--problem", str(backward_problem), "--quiet"],
                         capture_output=True, text=True, timeout=20,
                         env=dict(os.environ, AXIOM_SLICES="unit=0"))
    assert bad.returncode == 2 and "AXIOM_SLICES" in bad.stderr, bad
    # Splitting participates in the default search. Its final refutation may
    # close through either the preserved global FO path or the Boolean solver.
    avatar_problem = temp / "avatar.p"
    # Binary equivalences can now close during admission. A three-atom cube still
    # splits and records Boolean conflicts, but its final certificate currently
    # closes on the FO path, so the AVATAR export checks below are conditional.
    avatar_problem.write_text("\n".join(
        f"cnf(c{i},axiom,(" + "|".join(("~" if i & (1 << j) else "") + f"p{j}"
                                     for j in range(3)) + "))."
        for i in range(8)))
    out = run(fuzz, "--problem", avatar_problem, "--quiet",
              "--certificate", cert, "--metrics", metrics, "--rocq", rocq, "--tstp", tstp)
    assert "Result: UNSAT" in out and "VERIFIED" in run(replay, cert, "--problem", avatar_problem)
    report = next(csv.DictReader(metrics.open()))
    assert report["avatar_enabled"] == "true" and int(report["avatar_boolean_proof_nodes"]) > 0
    assert int(report["avatar_components"]) >= 2
    if "avatar_conflict" in tstp.read_text():
        assert int(report["avatar_conflicts"]) >= 2
    assert "source_axioms_unsatisfiable" in rocq.read_text() and "theory_refuted" in rocq.read_text()
    assert ("avatar_check_sources" in rocq.read_text()) == ("avatar_conflict" in tstp.read_text())
    assert "VERIFIED" in run(minimize, cert, "--problem", avatar_problem, "--output", small, "--seconds", "0.1")
    assert "VERIFIED" in run(replay, small, "--problem", avatar_problem)
    # Guided proposals use an additional budget, with attribution in CSV.
    out = run(fuzz, "--theory", "naive", "--max-instances", "4",
              "--workers", "2",               "--certificate", cert, "--metrics", metrics, "--worker-metrics", workers,
              "--schema-metrics", schemas, "--quiet")
    assert "Result: UNSAT" in out and "VERIFIED" in run(replay, cert)
    report = next(csv.DictReader(metrics.open()))
    assert report["guided"] == "true"
    worker_rows = list(csv.DictReader(workers.open()))
    assert len(worker_rows) == 2
    for row in worker_rows:
        assert int(row["exhaustive_instances"]) <= 4 and int(row["guided_instances"]) <= 4
        assert int(row["injected_instances"]) == int(row["exhaustive_instances"]) + int(row["guided_instances"])
    for row in csv.DictReader(schemas.open()):
        assert int(row["injected"]) == int(row["exhaustive_injected"]) + int(row["guided_injected"])
        assert int(row["candidates"]) == int(row["exhaustive_candidates"]) + int(row["guided_candidates"])
    # History is replayed before use, and workers import its Source patterns
    # into their own arenas. It never supplies trusted extra premises.
    out = run(fuzz, "--theory", "naive", "--history", cert, "--max-instances", "4",
              "--workers", "2",               "--metrics", metrics, "--quiet")
    assert "Result: UNSAT" in out
    report = next(csv.DictReader(metrics.open()))
    assert report["result"] == "UNSAT"
    run(fuzz, "--theory", "zf", "--history", cert, "--quiet", code=2)
    # The given-clause cap, not the wall clock, ends these searches (stopped cost clock, no
    # reference worker), so they do the same work on a loaded machine.
    capped = {"AXIOM_MEASURE_COST_CLOCK": "stopped", "AXIOM_MEASURE_REFERENCE": "off"}
    run(fuzz, "--theory", "zf", "--max-instances", "4", "--seconds", "60", "--max-given", "40",
        "--metrics", metrics, "--quiet", env=capped)
    report = next(csv.DictReader(metrics.open()))
    assert report["result"] == "UNKNOWN"
    assert int(report["guidance_matches"]) >= 0
    run(fuzz, "--theory", "zf", "--max-instances", "4", "--seconds", "60", "--max-given", "20",
        "--metrics", metrics, "--quiet", env=capped)
    report = next(csv.DictReader(metrics.open()))
    assert report["result"] == "UNKNOWN" and report["guided_compounds"] == "true"
    assert int(report["guidance_candidates"]) > 0 and int(report["guided_instances"]) <= 4
    # The default output is a summary; --stats adds the measurement lines (docs/cli.md).
    summary = run(fuzz, "--theory", "separation", "--seconds", "0.5", "--quiet")
    assert summary.startswith("Theory: separation\nResult: UNKNOWN\nReason: "), summary
    assert "[lane: " not in summary and "Metrics:" not in summary and "Heuristic 0:" not in summary
    assert "Proof source:" not in summary and "Reference:" not in summary, summary
    detailed = run(fuzz, "--theory", "separation", "--seconds", "0.5", "--quiet", "--stats")
    assert "[lane: " in detailed and "Metrics: " in detailed and "Heuristic 0: " in detailed
    assert "Proof source: none" in detailed and "Reference: ticks=" in detailed, detailed
    proved = run(fuzz, "--theory", "naive", "--quiet", "--output", small)
    assert proved.splitlines() == ["Theory: naive", "Result: UNSAT", "Reason: refutation verified",
                                   "Used axioms: comprehension_1", "Proof clauses: 5",
                                   f"Certificate: {small}"], proved
    assert "VERIFIED" in run(replay, small)
    # Every tool prints the release of axiom-fuzzer.opam; errors are one "Error: " line, exit 2.
    opam = (fixture_root.parent / "axiom-fuzzer.opam").read_text()
    release = next(line.split('"')[1] for line in opam.splitlines() if line.startswith("version:"))
    for tool, name in ((fuzz, "axiom-fuzz"), (replay, "axiom-replay"), (minimize, "axiom-minimize"),
                       (mutate, "axiom-mutate"), (reference, "axiom-reference")):
        assert run(tool, "--version") == f"{name} {release}\n", tool
    unknown = subprocess.run([str(fuzz), "--theory", "nonsense"], capture_output=True, text=True,
                             timeout=60)
    assert unknown.returncode == 2 and unknown.stderr.startswith("Error: Unknown theory: nonsense "), unknown
    assert "naive, separation, separation-universal, foundation-self, mutated-separation, zf" in unknown.stderr
    taken = temp / "taken"
    taken.mkdir()
    exists = subprocess.run([str(mutate), "--output-dir", str(taken)], capture_output=True, text=True,
                            timeout=60)
    assert exists.returncode == 2 and exists.stderr.startswith("Error: mkdir "), exists
    # An output that cannot be written is one Error line naming the path asked for, not the
    # temporary file beside it.
    missing = temp / "missing" / "naive.cert"
    unwritable = subprocess.run([str(fuzz), "--theory", "naive", "--quiet", "--certificate", str(missing)],
                                capture_output=True, text=True, timeout=60)
    assert unwritable.returncode == 2, unwritable
    assert unwritable.stderr == f"Error: {missing}: No such file or directory\n", unwritable.stderr
    help_text = run(fuzz, "--help")
    # Usage lines name the installed executables.
    assert help_text.startswith("axiom-fuzz [options]\n")
    assert run(replay, "--help").startswith("axiom-replay [options] FILE\n")
    assert run(minimize, "--help").startswith("axiom-minimize FILE --output FILE\n")
    assert ("--theory NAME Built-in theory: naive, separation, separation-universal, foundation-self, "
            "mutated-separation, zf (default naive)\n") in run(reference, "--help")
    for flag in ["--avatar", "--ordered", "--cnf", "--guided", "--reference-only", "--no-reference", "--clause-weight"]:
        assert flag not in help_text
        run(fuzz, flag, code=2)
    # Evaluation-only worker strategies stay out of --help and reject unknown names.
    assert "--eval-strategies" not in help_text
    run(fuzz, "--theory", "naive", "--eval-strategies", "unknown", "--quiet", code=2)
    run(fuzz, "--theory", "naive", "--eval-strategies", "production,calc:e", "--quiet", code=2)
    for spec, workers_, expected in [("production", "2", ["production", "production"]),
                                     ("balanced", "1", ["production"]),
                                     ("balanced", "4", ["production", "production", "e208", "y1346"]),
                                     ("production,production,e208,y1346", "4",
                                      ["production", "production", "e208", "y1346"]),
                                     ("calc:e", "1", ["calc:e"]),
                                     ("calc:e,production", "2", ["calc:e", "production"]),
                                     ("standard", "4", ["production", "calc:e", "production", "production"]),
                                     ("production,calc:e,production,production", "4",
                                      ["production", "calc:e", "production", "production"]),
                                     ("e208,production,y1346,production", "4",
                                      ["e208", "production", "y1346", "production"])]:
        run(fuzz, "--theory", "naive", "--quiet", "--workers", workers_, "--eval-strategies", spec,
            "--worker-metrics", workers)
        assert [w["strategy"] for w in csv.DictReader(workers.open())] == expected, spec
    # Each worker of the E composition runs its own strategy at its own queue phase (its index),
    # as a forked process by default and as a Domain under the A/A switch. Only the E workers
    # report queue-mix selections.
    composition = ["e208", "production", "y1346", "production"]
    for isolation in ("processes", "domains"):
        env = dict(os.environ, AXIOM_MEASURE_PORTFOLIO=isolation)
        out = subprocess.run([str(fuzz), "--theory", "naive", "--quiet", "--workers", "4",
                              "--eval-strategies", ",".join(composition), "--metrics", str(metrics),
                              "--worker-metrics", str(workers)],
                             env=env, capture_output=True, text=True, timeout=20)
        assert out.returncode == 0 and "Result: UNSAT" in out.stdout, (isolation, out)
        rows = list(csv.DictReader(workers.open()))
        assert [(w["worker"], w["strategy"]) for w in rows] == list(
            zip(["0", "1", "2", "3"], composition)), (isolation, rows)
        assert [w["mix_selections"] != "" for w in rows] == [True, False, True, False], isolation
        summary = next(csv.DictReader(metrics.open()))
        assert summary["isolation"] == isolation and summary["strategy"] in composition, summary
    # The last --eval-strategies wins whole: standard and lists reset the base strategy
    # an earlier single name set.
    for specs, workers_, expected in [(["calc:e", "standard"], "3", ["production", "calc:e", "production"]),
                                      (["calc:e", "balanced"], "3", ["production", "production", "e208"]),
                                      (["e208", "production,y1346"], "2", ["production", "y1346"]),
                                      (["standard", "calc:e"], "2", ["calc:e", "calc:e"])]:
        flags = [arg for spec in specs for arg in ("--eval-strategies", spec)]
        run(fuzz, "--theory", "naive", "--quiet", "--workers", workers_, *flags, "--worker-metrics", workers)
        assert [w["strategy"] for w in csv.DictReader(workers.open())] == expected, specs
    # A deterministic E strategy named again runs at its next queue phase (its copy index), by one
    # name or in a list; more copies than its period (11 for e208) would repeat a search and are
    # refused before any worker starts.
    for spec, workers_, expected in [("e208", "2", ["e208", "e208"]),
                                     ("e208,production,e208", "3", ["e208", "production", "e208"])]:
        run(fuzz, "--theory", "naive", "--quiet", "--workers", workers_, "--eval-strategies", spec,
            "--worker-metrics", workers)
        assert [w["strategy"] for w in csv.DictReader(workers.open())] == expected, spec
    run(fuzz, "--theory", "naive", "--quiet", "--workers", "12", "--eval-strategies", "e208", code=2)
    run(fuzz, "--theory", "naive", "--quiet", "--workers", "12", "--eval-strategies", ",".join(["e208"] * 12),
        code=2)
    # Workers that repeat another worker's search are not hidden: all production repeats its queue
    # phases modulo 22 from 23 workers on, and the CLI warns (the default rule from 45 workers on).
    quiet = subprocess.run([str(fuzz), "--theory", "naive", "--quiet", "--workers", "22", "--eval-strategies",
                            "production", "--seconds", "5"], capture_output=True, text=True, timeout=60)
    assert quiet.returncode == 0 and "Result: UNSAT" in quiet.stdout and "Warning" not in quiet.stderr, quiet
    warned = subprocess.run([str(fuzz), "--theory", "naive", "--quiet", "--workers", "23", "--eval-strategies",
                             "production", "--seconds", "5"], capture_output=True, text=True, timeout=60)
    assert warned.returncode == 0 and "Result: UNSAT" in warned.stdout, warned
    assert ("Warning: 1 of 23 workers repeat another worker's search (production" in warned.stderr
            and "distinct searches up to 22 workers" in warned.stderr), warned.stderr
    # Natural certificates use the same CLI and report real deduction counts.
    natural_cert, natural_problem = temp / "natural.cert", temp / "natural.p"
    run(natural_fixture, "--export-minimize", natural_cert, natural_problem)
    assert "VERIFIED" in run(replay, natural_cert, "--problem", natural_problem)
    out = run(minimize, natural_cert, "--problem", natural_problem, "--output", small)
    assert "axioms=3 -> 2" in out and "steps=6 -> 3" in out
    assert "VERIFIED" in run(replay, small, "--problem", natural_problem)
    run(minimize, natural_cert, "--problem", natural_problem, "--output", small, "--seconds", "0")
    assert small.read_text() == natural_cert.read_text()
    # Mutants have their own durable theory; original input remains unchanged.
    mutation_problem = temp / "mutation-original.p"
    original_text = "fof(a,axiom,(p(a) | ~p(a))).\n"
    mutation_problem.write_text(original_text)
    mutants = temp / "mutants"
    out = run(mutate, "--problem", mutation_problem, "--output-dir", mutants,
              "--mutations", "6", "--observations", "0", "--seconds", "0.2")
    assert "result=UNSAT" in out and mutation_problem.read_text() == original_text
    proofs = list(mutants.glob("*.cert"))
    assert proofs
    for proof in proofs:
        assert "VERIFIED" in run(replay, proof, "--problem", proof.with_suffix(".p"))
        run(replay, proof, "--problem", mutation_problem, code=1)
    run(mutate, "--output-dir", temp / "bad-mutants", "--mutations", "-1", code=2)
    run(fuzz, "--theory", "naive", "--metrics", metrics, "--quiet")
    report = next(csv.DictReader(metrics.open()))
    assert int(report["proof_nodes"]) <= int(report["retained"])
    # Certified enumeration progresses after heuristic exhaustion and resumes.
    ref_problem = temp / "reference.p"
    ref_problem.write_text("fof(p,axiom,p(a)).\n")
    checkpoint = temp / "reference.checkpoint"
    previous = 0
    for _ in range(2):
        out = run(fuzz, "--problem", ref_problem, "--seconds", "0.05",
                  "--checkpoint", checkpoint, "--metrics", metrics, "--quiet", "--stats")
        report = next(csv.DictReader(metrics.open()))
        assert report["result"] == "UNKNOWN"
        current = int(report["reference_cumulative_trials"])
        assert current > previous
        previous = current
        # reference_trials counts this run in stdout and CSV alike, also after resuming.
        ticks = fields(out, "Reference")["ticks"]
        assert fields(out, "Metrics")["reference_trials"] == ticks == report["reference_trials"]
    assert "resumed=true" in out
    with pathlib.Path(str(checkpoint) + ".lock").open("w") as lock:
        fcntl.lockf(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        run(fuzz, "--problem", ref_problem, "--checkpoint", checkpoint, code=2)
    ref_problem.write_text("fof(q,axiom,q(a)).\n")
    run(fuzz, "--problem", ref_problem, "--checkpoint", checkpoint, code=2)
    checkpoint.unlink()
    process = subprocess.Popen([str(fuzz), "--problem", str(ref_problem), "--seconds", "30",
                                "--checkpoint", str(checkpoint), "--quiet"],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        deadline = time.monotonic() + 10
        while not checkpoint.exists() and process.poll() is None and time.monotonic() < deadline:
            time.sleep(0.01)
        assert checkpoint.exists(), "no periodic checkpoint"
        os.kill(process.pid, signal.SIGINT)
        stdout, stderr = process.communicate(timeout=10)
        assert process.returncode == 0 and "Result: UNKNOWN" in stdout, (stdout, stderr)
        assert "cancelled" in stdout
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert "resumed=true" in run(fuzz, "--problem", ref_problem, "--seconds", "0.02",
                                 "--checkpoint", checkpoint, "--quiet", "--stats")
    cert.write_text('(axiom-fuzzer "naive")')
    run(replay, cert, code=2)
print("ok  CLI, fixtures, roundtrip exports, external manifest, and durable artifacts")
