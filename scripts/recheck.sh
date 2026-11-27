#!/bin/sh
# Re-check an axiom-fuzzer certificate independently of the search that produced it.
#
# usage: scripts/recheck.sh (--theory NAME | --problem FILE) CERT
#
#   1. axiom-replay checks CERT in a fresh process against the theory or problem that you
#      name. The certificate is never its own authority: name the theory, or pass the exact
#      original TPTP file that was solved.
#   2. axiom-replay --rocq exports the refutation as a Rocq source file.
#   3. The Rocq development in rocq/ is compiled, the export is compiled against it, and every
#      Print Assumptions result (of the library and of the export) is audited with
#      scripts/rocq_assumptions.py.
#
# Step 3 takes the extraction, the OCaml compiler and the OCaml runtime out of the trusted
# base for this certificate. What stays trusted is listed in docs/guarantees.md.
#
# Environment:
#   AXIOM_REPLAY      the axiom-replay binary (default: build it with dune in this checkout)
#   ROCQ              the rocq binary: Rocq 9.3.0 with its Stdlib (default: found by
#                     scripts/find_rocq.sh on the PATH, in the opam switches or in Homebrew)
#   RECHECK_ROCQ_LIB  a directory that keeps the compiled rocq/ library between runs
#                     (default: a temporary directory, removed at exit)
#   RECHECK_KEEP      set to keep the temporary work directory and print its path
#
# This script only reads the repository; it changes no file in it.
set -eu

usage() {
  echo "usage: $0 (--theory NAME | --problem FILE) CERT" >&2
  exit 2
}

[ $# -eq 3 ] || usage
case $1 in
--theory | --problem) ;;
*) usage ;;
esac
mode=$1
target=$2
cert=$3
[ -f "$cert" ] || { echo "Error: certificate not found: $cert" >&2; exit 2; }
if [ "$mode" = --problem ]; then
  [ -f "$target" ] || { echo "Error: problem not found: $target" >&2; exit 2; }
fi

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/axiom-fuzzer-recheck.XXXXXX")
if [ -n "${RECHECK_KEEP:-}" ]; then
  echo "Work directory: $work"
else
  trap 'rm -rf "$work"' EXIT HUP INT TERM
fi

# Step 1: a separate replay process.
replay=${AXIOM_REPLAY:-}
if [ -z "$replay" ]; then
  (cd "$root" && dune build ./_build/default/bin/replay/main.exe) >&2
  replay=$root/_build/default/bin/replay/main.exe
fi
echo "== 1. axiom-replay ($replay)"
status=0
"$replay" "$mode" "$target" "$cert" || status=$?
if [ $status -ne 0 ]; then
  echo "Recheck: axiom-replay did not verify the certificate (exit $status)." >&2
  exit $status
fi

# Step 2: export the refutation as Rocq source.
echo "== 2. axiom-replay --rocq"
"$replay" "$mode" "$target" --rocq "$work/Refutation.v" "$cert" > /dev/null
echo "Exported $(wc -c < "$work/Refutation.v" | tr -d ' ') bytes of Rocq source."

# Step 3: compile the Rocq library, then the export, and audit the assumptions.
. "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/find_rocq.sh"
find_rocq || exit 2
rocq=$rocq_path
case $rocq in
*/*) PATH=$(CDPATH= cd -- "$(dirname -- "$rocq")" && pwd):$PATH; export PATH ;;
esac
echo "== 3. Rocq ($("$rocq" --version 2>/dev/null | head -n 1))"
printf 'From Stdlib Require Import List.\n' > "$work/StdlibProbe.v"
if ! (cd "$work" && "$rocq" compile -q StdlibProbe.v) > /dev/null 2>&1; then
  echo "Error: $rocq cannot load its Stdlib. Rocq 9 ships the Stdlib separately" >&2
  echo "(opam package rocq-stdlib); install it or point ROCQ at a Rocq that has it." >&2
  exit 2
fi
lib=${RECHECK_ROCQ_LIB:-$work/lib}
mkdir -p "$lib"
# Keep each library file's compiler output next to it (rocq_assumptions.py reads FILE.v.out).
cat > "$work/capture.sh" << 'EOF'
#!/bin/sh
for last; do :; done
case $last in
*.v) ;;
*) exec "$@" ;;
esac
"$@" > "$last.out"
status=$?
cat "$last.out"
exit $status
EOF
chmod +x "$work/capture.sh"
python3 - "$root" "$lib" "$work/capture.sh" << 'PY'
from pathlib import Path
import filecmp
import shutil
import subprocess
import sys

root, lib, capture = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
files = []
for path in sorted((root / "rocq").rglob("*.v")):
    relative = Path("rocq") / path.relative_to(root / "rocq")
    target = lib / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    if not target.exists() or not filecmp.cmp(path, target, shallow=False):
        shutil.copy2(path, target)
    files.append(str(relative))
subprocess.run(["rocq", "makefile", "--no-rocq-package-warning", "-docroot", "AxiomFuzzer",
                "-Q", "rocq", "AxiomFuzzer", *files, "-o", "Makefile.rocq"], cwd=lib, check=True,
               stdout=subprocess.DEVNULL)
subprocess.run(["make", "-f", "Makefile.rocq", "-j", "4", "TIMED=", "TIMECMD=" + capture],
               cwd=lib, check=True, stdout=subprocess.DEVNULL)
PY
echo "Compiled the rocq/ library in $lib."
(cd "$work" && "$rocq" compile -q -Q "$lib/rocq" AxiomFuzzer Refutation.v > Refutation.v.out)
grep -E '^(Closed under the global context|Axioms:)' "$work/Refutation.v.out" | sort | uniq -c
python3 "$root/scripts/rocq_assumptions.py" "$lib" "$work/Refutation.v"
echo "Recheck: VERIFIED by axiom-replay and by Rocq."
echo "Compare the source axioms or theory manifest printed in the export with your input"
if [ -n "${RECHECK_KEEP:-}" ]; then
  echo "(names are printed as byte lists): $work/Refutation.v"
else
  echo "(names are printed as byte lists); set RECHECK_KEEP=1 to keep the export."
fi
