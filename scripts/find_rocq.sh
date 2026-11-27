# Find the Rocq toolchain; sourced by check_rocq.sh and recheck.sh (POSIX sh).
#
# find_rocq [prefer-ocaml]
#   With ROCQ set, use exactly that rocq (a name on the PATH or a path) and fail if it is
#   unusable. Otherwise try, in order, every rocq on the PATH, the rocq of every opam switch, and
#   /opt/homebrew/bin/rocq and /usr/local/bin/rocq. A candidate must be Rocq 9.3.0 with a compiled
#   Stdlib. Among those, the first built with OCaml PREFER-OCAML (for example 5.5) wins; without
#   one, the first usable candidate is taken with a warning. Sets rocq_path and rocq_stdlib, and
#   reports skipped candidates on standard error.

rocq_version_required=9.3.0

# Prints the reason a candidate is unusable, or nothing if it is usable.
rocq_unusable() {
  version=$("$1" --version 2>/dev/null) || { echo "does not run"; return; }
  case $version in
  *"version $rocq_version_required"*) ;;
  *) echo "is not Rocq $rocq_version_required"; return ;;
  esac
  where=$("$1" compile -where 2>/dev/null) || { echo "cannot report its library directory"; return; }
  [ -f "$where/user-contrib/Stdlib/Lists/List.vo" ] ||
    echo "has no compiled Stdlib in $where/user-contrib/Stdlib (install rocq-stdlib 9.2.0)"
}

rocq_ocaml() {
  "$1" --version 2>/dev/null | sed -n 's/.*compiled with OCaml \([0-9][0-9.]*\).*/\1/p'
}

rocq_candidates() {
  ( IFS=:; for dir in $PATH; do [ -x "${dir:-.}/rocq" ] && echo "${dir:-.}/rocq"; done )
  if command -v opam > /dev/null 2>&1; then
    for switch in $(opam switch list --short 2>/dev/null); do
      bin=$(opam var --switch="$switch" bin 2>/dev/null) && [ -x "$bin/rocq" ] && echo "$bin/rocq"
    done
  fi
  for path in /opt/homebrew/bin/rocq /usr/local/bin/rocq; do [ -x "$path" ] && echo "$path"; done
}

find_rocq() {
  prefer=${1:-}
  if [ -n "${ROCQ:-}" ]; then
    if ! rocq_path=$(command -v "$ROCQ"); then
      echo "Rocq: ROCQ=$ROCQ was not found." >&2
      return 1
    fi
    reason=$(rocq_unusable "$rocq_path")
    if [ -n "$reason" ]; then
      echo "Rocq: ROCQ=$rocq_path $reason." >&2
      return 1
    fi
  else
    rocq_path= fallback= seen=
    for candidate in $(rocq_candidates); do
      resolved=$(cd "$(dirname "$candidate")" && pwd -P)/$(basename "$candidate")
      case " $seen " in *" $resolved "*) continue ;; esac
      seen="$seen $resolved"
      reason=$(rocq_unusable "$candidate")
      if [ -n "$reason" ]; then
        echo "Rocq: skipping $candidate: it $reason." >&2
        continue
      fi
      case $(rocq_ocaml "$candidate") in
      "$prefer" | "$prefer".*) rocq_path=$candidate; break ;;
      esac
      [ -n "$prefer" ] && echo "Rocq: skipping $candidate for now: built with OCaml $(rocq_ocaml "$candidate"), not $prefer." >&2
      [ -n "$fallback" ] || fallback=$candidate
    done
    if [ -z "$rocq_path" ]; then
      if [ -z "$fallback" ]; then
        echo "Rocq: no usable Rocq $rocq_version_required with its Stdlib was found on the PATH, in" \
          "the opam switches or in Homebrew. Install rocq-core.9.3.0 and rocq-stdlib.9.2.0, or set" \
          "ROCQ to a rocq executable." >&2
        return 1
      fi
      rocq_path=$fallback
      [ -n "$prefer" ] && echo "Rocq: warning: using $rocq_path, built with OCaml $(rocq_ocaml "$rocq_path"), not $prefer." >&2
    fi
  fi
  rocq_stdlib="$("$rocq_path" compile -where)/user-contrib/Stdlib"
}
