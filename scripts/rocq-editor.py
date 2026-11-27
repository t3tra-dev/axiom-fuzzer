#!/usr/bin/env python3
"""Build editor dependencies with VsRocq's toolchain, then start the server.

VS Code's VsRocq runs this script as its language server (.vscode/settings.json, vsrocq.path);
`make rocq-editor` runs `rocq-editor.py --build`. The Rocq files of rocq/ (and, if the switch has
no compiled Stdlib, a Stdlib copied from its sources) are compiled into _build/rocq-editor with
the same Rocq and OCaml as the server, which _RocqProject maps to the logical path AxiomFuzzer.

Overrides (environment variables):
  AXIOM_FUZZER_ROCQ_SWITCH  the opam switch whose rocq and vsrocqtop to use; by default opam's
                            active switch, or the tools on PATH when opam is not installed.
  AXIOM_FUZZER_STDLIB_SOURCE  a directory of Stdlib sources (with Lists/List.v) to build when the
                            switch has no compiled Stdlib. Without it the script tries the
                            switch's own user-contrib/Stdlib and the Stdlib sources that
                            Homebrew's Rocq installs under /opt/homebrew or /usr/local.
"""

import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "_build" / "rocq-editor"
# The Rocq toolchain: the opam switch named by AXIOM_FUZZER_ROCQ_SWITCH; otherwise opam's active
# switch; without opam, the tools on PATH.
SWITCH = os.environ.get("AXIOM_FUZZER_ROCQ_SWITCH") or None
if SWITCH:
    OPAM = ["opam", "exec", "--switch=" + SWITCH, "--"]
elif shutil.which("opam"):
    OPAM = ["opam", "exec", "--"]
else:
    OPAM = []


def output(*args):
    return subprocess.check_output(OPAM + list(args), text=True, cwd=ROOT).strip()


def stdlib_source():
    """Prefer the switch's compiled Stdlib; otherwise rebuild local sources."""
    installed = Path(output("rocq", "compile", "-where")) / "user-contrib/Stdlib"
    if (installed / "Lists/List.vo").is_file():
        return None
    override = os.environ.get("AXIOM_FUZZER_STDLIB_SOURCE")
    candidates = [Path(override)] if override else [
        installed,
        Path("/opt/homebrew/lib/ocaml/coq/user-contrib/Stdlib"),
        Path("/usr/local/lib/ocaml/coq/user-contrib/Stdlib"),
    ]
    for candidate in candidates:
        if (candidate / "Lists/List.v").is_file():
            return candidate.resolve()
    raise RuntimeError(
        "no Stdlib found: run opam install " + ("--switch=" + SWITCH + " " if SWITCH else "")
        + "rocq-stdlib, or set AXIOM_FUZZER_STDLIB_SOURCE to a compatible Stdlib source directory"
    )


def prepare():
    # Keep parallel editor/task launches from writing the same object files.
    BUILD.parent.mkdir(parents=True, exist_ok=True)
    with (BUILD.parent / ".rocq-editor.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        stdlib = stdlib_source()
        sources = [(path, path.relative_to(ROOT))
                   for path in sorted((ROOT / "rocq").rglob("*.v"))]
        if stdlib is not None:
            sources += [(path, Path("stdlib") / path.relative_to(stdlib))
                        for path in sorted(stdlib.rglob("*.v"))]

        # Rocq .vo files depend on the OCaml toolchain as well as Rocq itself.
        # Invalidate this private build directory when either changes, or when
        # files disappear so that stale modules cannot remain importable.
        manifest = json.dumps({
            "switch": SWITCH or ("active" if OPAM else "PATH"),
            "rocq": output("rocq", "--version"),
            "config": output("rocq", "compile", "-config"),
            "stdlib_source": str(stdlib) if stdlib else None,
            "sources": [str(path) for _, path in sources],
        }, sort_keys=True, indent=2)
        stamp = BUILD / "toolchain.json"
        if not stamp.exists() or stamp.read_text() != manifest:
            if BUILD.exists():
                shutil.rmtree(BUILD)
            BUILD.mkdir(parents=True)
            stamp.write_text(manifest)
        # Compare contents: restoring an older file must also trigger a rebuild.
        for source, relative in sources:
            target = BUILD / relative
            data = source.read_bytes()
            if not target.exists() or target.read_bytes() != data:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)

        loadpath = ["-R", "stdlib", "Stdlib"] if stdlib else []
        makefile = ["rocq", "makefile", "--no-rocq-package-warning",
                    "-docroot", "AxiomFuzzer", *loadpath,
                    "-Q", "rocq", "AxiomFuzzer",
                    *(str(path) for _, path in sources), "-o", "Makefile.rocq"]
        targets = [str(path.with_suffix(".vo")) for _, path in sources
                   if path.parts[0] == "rocq"]
        log_path = BUILD / "build.log"
        with log_path.open("w") as log:
            for command in [makefile, ["make", "-f", "Makefile.rocq", "-j", "4", *targets]]:
                result = subprocess.run(OPAM + command, cwd=BUILD, stdout=log,
                                        stderr=subprocess.STDOUT)
                if result.returncode:
                    log.flush()
                    print(log_path.read_text()[-6000:], file=sys.stderr)
                    print("Rocq editor build failed; see " + str(log_path),
                          file=sys.stderr)
                    # A proof being edited may be incomplete. Still start LSP
                    # so it can show the error and help the user fix it.
                    return stdlib, False
        return stdlib, True


def main():
    args = sys.argv[1:]
    os.chdir(ROOT)
    # VsRocq probes the version/location before opening its LSP connection.
    probes = {"-where", "-v", "--version", "-print-version", "-config", "--config",
              "-help", "--help", "-h"}
    if any(arg in probes for arg in args):
        command = OPAM + ["vsrocqtop", *args]
        os.execvp(command[0], command)
    stdlib, success = prepare()
    if args == ["--build"]:
        if success:
            print("Rocq editor: Stdlib and the project's dependencies are ready.")
        return 0 if success else 1
    loadpath = ["-R", str(BUILD / "stdlib"), "Stdlib"] if stdlib else []
    # Build output must never be written to stdout: it carries the LSP protocol.
    command = OPAM + ["vsrocqtop", *loadpath, *args]
    os.execvp(command[0], command)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print("Rocq editor: " + str(error), file=sys.stderr)
        sys.exit(1)
