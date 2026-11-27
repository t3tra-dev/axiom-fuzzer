#!/bin/sh
set -eu
task_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
# The Rocq toolchain: ROCQ names the rocq executable (default: the first rocq on PATH). Set it
# instead of reordering PATH, which would also change the OCaml compiler that dune runs.
ROCQ=${ROCQ:-rocq}
if ! rocq_path=$(command -v "$ROCQ"); then
  echo "Rocq: $ROCQ was not found. Install Rocq 9.3.0 built with OCaml 5.5 and its Stdlib 9.2.0" \
    "(opam install rocq-core.9.3.0 rocq-stdlib.9.2.0), or set ROCQ to its rocq executable." >&2
  exit 1
fi
rocq_stdlib="$("$rocq_path" compile -where)/user-contrib/Stdlib"
if [ ! -f "$rocq_stdlib/Lists/List.vo" ]; then
  echo "Rocq: $rocq_path has no compiled Stdlib in $rocq_stdlib. Install rocq-stdlib 9.2.0 for it" \
    "(opam install rocq-stdlib.9.2.0), or set ROCQ to a rocq that has one." >&2
  exit 1
fi
echo "Rocq: $("$rocq_path" --version | tr '\n' ' ')($rocq_path; Stdlib $rocq_stdlib)"
task_temp=$(mktemp -d "${TMPDIR:-/tmp}/axiom-fuzzer-rocq.XXXXXX")
trap 'rm -rf "$task_temp"' EXIT HUP INT TERM
# Parallel make interleaves compiler output, so keep each file's stdout next to it.
# Makefile.rocq runs every tool through TIMECMD; only a .v compilation is captured.
cat > "$task_temp/capture.sh" <<'EOF'
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
chmod +x "$task_temp/capture.sh"
python3 - "$task_root" "$task_temp" "$rocq_path" <<'PY'
from pathlib import Path
import shutil
import subprocess
import sys

root, build, rocq = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
source = root / "rocq"
files = []
for path in sorted(source.rglob("*.v")):
    relative = Path("rocq") / path.relative_to(source)
    target = build / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, target)
    files.append(str(relative))
subprocess.run([rocq, "makefile", "--no-rocq-package-warning", "-docroot", "AxiomFuzzer",
                "-Q", "rocq", "AxiomFuzzer", *files, "-o", "Makefile.rocq"], cwd=build, check=True)
# TIMED= keeps TIMECMD in use when TIMED is set in the environment; COQBIN selects this rocq.
subprocess.run(["make", "-f", "Makefile.rocq", "-j", "4", "TIMED=", "TIMECMD=" + str(build / "capture.sh"),
                "COQBIN=" + str(Path(rocq).parent) + "/"],
               cwd=build, check=True)
PY
cmp "$task_temp/rocq_checker.ml" "$task_root/lib/proof/rocq_checker.ml"
cmp "$task_temp/rocq_checker.mli" "$task_root/lib/proof/rocq_checker.mli"
cmp "$task_temp/avatar_checker.ml" "$task_root/lib/proof/avatar_checker.ml"
cmp "$task_temp/avatar_checker.mli" "$task_root/lib/proof/avatar_checker.mli"
cmp "$task_temp/source_checker.ml" "$task_root/lib/syntax/source_checker.ml"
cmp "$task_temp/source_checker.mli" "$task_root/lib/syntax/source_checker.mli"
cmp "$task_temp/wire_checker.ml" "$task_root/lib/proof/wire_checker.ml"
cmp "$task_temp/wire_checker.mli" "$task_root/lib/proof/wire_checker.mli"
cmp "$task_temp/wire_normalizer.ml" "$task_root/lib/proof/wire_normalizer.ml"
cmp "$task_temp/wire_normalizer.mli" "$task_root/lib/proof/wire_normalizer.mli"
cmp "$task_temp/kernel_checker.ml" "$task_root/lib/proof/kernel_checker.ml"
cmp "$task_temp/kernel_checker.mli" "$task_root/lib/proof/kernel_checker.mli"
cmp "$task_temp/natural_checker.ml" "$task_root/lib/proof/natural_checker.ml"
cmp "$task_temp/natural_checker.mli" "$task_root/lib/proof/natural_checker.mli"
proofs=0
# Compile a generated proof and keep it with its output for the assumption audit.
compile_proof() {
  "$rocq_path" compile -q -Q "$task_temp/rocq" AxiomFuzzer "$1" > "$1.out"
  cat "$1.out"
  proofs=$((proofs + 1))
  mkdir -p "$task_temp/audit/$proofs"
  cp "$1" "$1.out" "$task_temp/audit/$proofs/"
}
# A fixed example must keep exercising the rule it is named after.
require() {
  grep -q "$1" "$2" || { echo "Rocq: $(basename "$2") does not contain $1" >&2; exit 1; }
}
for theory in naive separation-universal foundation-self; do
  "$task_root/bin/fuzz/main.exe" --theory "$theory" --quiet --rocq "$task_temp/Refutation.v" > "$task_temp/search.log"
  compile_proof "$task_temp/Refutation.v"
done
"$task_root/bin/fuzz/main.exe" --problem "$task_root/theories/examples/equality.p" --quiet --rocq "$task_temp/EqualityRefutation.v" > "$task_temp/search.log"
compile_proof "$task_temp/EqualityRefutation.v"
"$task_root/bin/fuzz/main.exe" --problem "$task_root/theories/examples/definitions.p" --quiet --rocq "$task_temp/DefinitionRefutation.v" > "$task_temp/search.log"
require DefinitionalEvidence "$task_temp/DefinitionRefutation.v"
compile_proof "$task_temp/DefinitionRefutation.v"
"$task_root/bin/fuzz/main.exe" --problem "$task_root/theories/examples/equality-factoring.p" --quiet --rocq "$task_temp/FactoringRefutation.v" > "$task_temp/search.log"
require Equality_factor "$task_temp/FactoringRefutation.v"
compile_proof "$task_temp/FactoringRefutation.v"
"$task_root/bin/fuzz/main.exe" --problem "$task_root/theories/examples/backward-demodulation.p" --quiet --rocq "$task_temp/BackwardRefutation.v" --metrics "$task_temp/backward.csv" > "$task_temp/search.log"
python3 - "$task_temp/backward.csv" <<'PY'
import csv
import sys

row = next(csv.DictReader(open(sys.argv[1])))
if int(row["backward_demodulated"]) < 1:
    sys.exit("Rocq: backward-demodulation.p no longer rewrites an Active clause backward")
PY
compile_proof "$task_temp/BackwardRefutation.v"
"$task_root/bin/fuzz/main.exe" --theory naive --max-instances 4 --quiet --rocq "$task_temp/GuidedRefutation.v" > "$task_temp/search.log"
compile_proof "$task_temp/GuidedRefutation.v"
"$task_root/tests/regression/theory_tests.exe" --export-rocq "$task_temp/RegisteredRefutation.v"
compile_proof "$task_temp/RegisteredRefutation.v"
"$task_root/tests/regression/natural_tests.exe" --export-rocq "$task_temp/NaturalRefutation.v"
compile_proof "$task_temp/NaturalRefutation.v"
"$task_root/tests/regression/theory_tests.exe" --export-enumerated "$task_temp/EnumeratedRefutation.v"
compile_proof "$task_temp/EnumeratedRefutation.v"
"$task_root/tests/regression/theory_tests.exe" --export-enumerated-natural "$task_temp/EnumeratedNatural.v"
compile_proof "$task_temp/EnumeratedNatural.v"
"$task_root/tests/regression/natural_tests.exe" --export-shrunk-rocq "$task_temp/ShrunkNatural.v"
compile_proof "$task_temp/ShrunkNatural.v"
"$task_root/tests/regression/extensions_tests.exe" --export-rocq "$task_temp/DefinedRefutation.v"
require defined_theory_unsatisfiable "$task_temp/DefinedRefutation.v"
compile_proof "$task_temp/DefinedRefutation.v"
"$task_root/tests/regression/avatar_proof_tests.exe" --export-rocq "$task_temp/AvatarRefutation.v"
compile_proof "$task_temp/AvatarRefutation.v"
# AVATAR runs during this default search; its final proof currently closes on the
# FO path. Engine-made AVATAR certificates come from unified_tests and goal_tests.
cat > "$task_temp/AvatarEngine.p" <<'EOF'
fof(choice,axiom,((![X]:p(X)) | (![Y]:q(Y)))).
fof(not_p,axiom,~p(a)).
fof(not_q,axiom,~q(b)).
EOF
"$task_root/bin/fuzz/main.exe" --problem "$task_temp/AvatarEngine.p" --quiet --rocq "$task_temp/AvatarEngineRefutation.v" > "$task_temp/search.log"
compile_proof "$task_temp/AvatarEngineRefutation.v"
"$task_root/tests/regression/unified_tests.exe" --export-rocq "$task_temp"
compile_proof "$task_temp/SharedRefutation.v"
compile_proof "$task_temp/CongruentRefutation.v"
compile_proof "$task_temp/JointRefutation.v"
"$task_root/tests/regression/goal_tests.exe" --export-rocq "$task_temp"
for name in GoalRefutation GoalEqualityRefutation GoalSharedRefutation GoalAvatarRefutation GoalPromotedRefutation GoalFirstTrialRefutation; do
  compile_proof "$task_temp/$name.v"
done
"$task_root/tests/regression/contraction_tests.exe" --export-rocq "$task_temp/ContractionRefutation.v"
compile_proof "$task_temp/ContractionRefutation.v"
python3 "$task_root/scripts/rocq_assumptions.py" "$task_temp" "$task_temp"/audit/*/*.v
# The audit must keep rejecting known holes in this Rocq's real output: every
# source_* file fails the full audit, and every output_* file also fails from its
# compiler output alone (its source reduced to the Print Assumptions commands).
holes=0
for file in "$task_root"/tests/fixtures/rocq_audit/*.v; do
  name=$(basename "$file" .v)
  case_root="$task_temp/holes/$name"
  mkdir -p "$case_root/rocq"
  cp "$file" "$case_root/rocq/"
  if ! (cd "$case_root/rocq" && "$rocq_path" compile -q "$name.v" > "$name.v.out" 2> "$name.v.err"); then
    cat "$case_root/rocq/$name.v.err" >&2
    exit 1
  fi
  if python3 "$task_root/scripts/rocq_assumptions.py" "$case_root" > /dev/null 2>&1; then
    echo "Rocq: the assumption audit accepted $name.v" >&2
    exit 1
  fi
  case $name in
  output_*)
    mkdir -p "$case_root-output/rocq"
    grep '^Print Assumptions' "$file" > "$case_root-output/rocq/$name.v"
    cp "$case_root/rocq/$name.v.out" "$case_root-output/rocq/"
    if python3 "$task_root/scripts/rocq_assumptions.py" "$case_root-output" > /dev/null 2>&1; then
      echo "Rocq: the assumption audit accepted the output of $name.v" >&2
      exit 1
    fi
    ;;
  esac
  holes=$((holes + 1))
done
echo "Rocq assumptions: the audit rejects all $holes known holes in tests/fixtures/rocq_audit."
printf '%s\n' "Rocq: soundness, standard FOL connection, enumerable theories, certificate completeness, eventual discovery with a streaming cursor, indexed replay equivalence, conditional replay with shared components and congruence explanations, general goal derivations, admission contraction, definition expansion, 7 reproducible extractions, and $proofs exported Source refutations verified."
