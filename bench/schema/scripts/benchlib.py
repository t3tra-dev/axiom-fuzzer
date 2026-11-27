"""Shared helpers for the schema benchmark scripts (stdlib only).

Variants are given as NAME=BINARY [FLAG ...], e.g.
    --variant 'lane-fifo=/path/schema_bench.exe --lane fifo'
so one frozen binary can be measured under several internal configurations.

Solver processes can be wrapped in a machine-wide slot pool: pass
--slots DIR (a directory containing slots.py with
`acquire(weight)` as a context manager), or set AXF_SLOTS_DIR. Without one,
processes run unthrottled (fine on a quiet machine).
"""
import contextlib
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path


def parse_variant(spec):
    if "=" not in spec:
        raise SystemExit(f"variant must be NAME=BINARY [FLAGS]: {spec}")
    name, rest = spec.split("=", 1)
    words = shlex.split(rest)
    if not words:
        raise SystemExit(f"variant {name} has no binary")
    binary = str(Path(words[0]).resolve())
    if not os.access(binary, os.X_OK):
        raise SystemExit(f"variant {name}: not executable: {binary}")
    return name, binary, words[1:]


def slot_pool(directory):
    directory = directory or os.environ.get("AXF_SLOTS_DIR")
    if not directory:
        return lambda weight: contextlib.nullcontext()
    sys.path.insert(0, str(Path(directory).resolve()))
    import slots  # noqa: E402

    return slots.acquire


def list_cases(binary):
    out = subprocess.run([binary, "list"], capture_output=True, text=True, check=True).stdout
    return [line.split()[0] for line in out.splitlines() if line.strip()]


RESULT = re.compile(r"case=(\S+) result=(\S+) seconds=(\S+)(.*)")


def parse_result(line):
    m = RESULT.match(line)
    if not m:
        return None
    rest = m.group(4)
    out = {"case": m.group(1), "result": m.group(2), "seconds": float(m.group(3))}
    for key in ("source", "check_seconds", "axioms"):
        k = re.search(rf"\b{key}=(\S+)", rest)
        if k:
            out[key] = k.group(1)
    inst = re.search(r"instances=\[(.*)\]\s*$", rest)
    if inst:
        out["instances"] = inst.group(1)
    lane = re.search(r"\[lane:[ _]([^\]]*)\]", rest)
    if lane:
        out["lane"] = lane.group(1).replace("_", " ")
    return out
