#!/usr/bin/env bash
set -euo pipefail
task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$task_root"
# Measured binaries use the release profile (see `make release`), in the default context only.
dune build --profile release ./_build/default/bin/fuzz/main.exe ./_build/default/bin/mutate/main.exe
exec python3 -B benchmarks/run.py --external all --runs 5 "$@"
