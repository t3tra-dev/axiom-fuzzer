# Installation

## Requirements

| Component | Version | Needed for |
| --- | --- | --- |
| OCaml | 5.2 to 5.5; tested with 5.2.1, 5.4.1 and 5.5.2 | everything (a C stub reads runtime internals whose layout was checked for 5.1 to 5.5) |
| Dune | 3.17 or later; tested with 3.17.2, 3.24.2 and 3.25.0 | everything |
| C compiler | Xcode Command Line Tools on macOS, gcc or clang on Linux | the clock, RSS and process-lifeline stubs |
| Python | 3.12 or later, standard library only | the test suite and the benchmark scripts (they need `tarfile` extraction filters) |
| `make`, `ps` (procps on Linux) | any | `make` targets, the process tests |
| Rocq | 9.3.0 with its Stdlib | `dune build @rocq` and the Rocq re-check |
| OCaml 5.5.2 + flambda | optional | the release build used for measurements |
| ocamlformat | 0.29.0 | `dune build @fmt` (contributors only; [how to install it](development.md#formatting)) |

The library depends only on the OCaml standard library and `unix`. Nothing else is downloaded
at build time.

## Platforms

| Platform | Status |
| --- | --- |
| macOS, arm64 | Developed and tested; all development measurements were taken here |
| Linux, x86_64 | Supported; the build and test suite passed in an ubuntu-24.04 container, and CI builds and tests on Linux |
| Windows | Not supported: the process portfolio needs `fork`, `setsid`, process groups and POSIX signals. WSL was not tried |

## Build from a fresh clone with opam

```sh
git clone https://github.com/t3tra-dev/axiom-fuzzer.git
cd axiom-fuzzer
opam switch create . 5.5.2 --no-install   # a local switch; any OCaml from 5.2 to 5.5 works
eval $(opam env)
opam install . --deps-only --with-test
dune build
dune runtest
```

`dune build` builds the five binaries, the library, the test executables and the benchmark
executables. `dune runtest` runs the deterministic test tier
([development.md](development.md#tests) has the others). Run the binaries with
`dune exec axiom-fuzz -- ARGS`, or install them with `opam install .`.

Without opam, an OCaml from 5.2 to 5.5 and Dune 3.17 or later on the `PATH` work the same way:
the repository's `dune-workspace` defines only the default context, which uses the compiler on
the `PATH` (also checked with an empty opam root). The editor context for VS Code is opt-in; see
[Editor setup](#editor-setup).

## Rocq, for the proofs

Two things use Rocq: `dune build @rocq`, which re-checks the whole Rocq development and the
extracted checkers, and the Rocq re-check of a single certificate
([scripts/recheck.sh](../scripts/recheck.sh), see [guarantees.md](guarantees.md)). Both need
Rocq 9.3.0 with its Stdlib. In Rocq 9 the Stdlib is a separate package; the pair that works is
`rocq-core` 9.3.0 with `rocq-stdlib` 9.2.0, which needs `gmp` and `pkg-config`:

```sh
opam install rocq-core.9.3.0 rocq-stdlib.9.2.0
rocq --version
```

- `dune build @rocq` compares the re-extracted checkers with the 14 files in `lib/` byte by
  byte. That comparison succeeds only with a Rocq built with OCaml 5.5.x: with a Rocq built
  with OCaml 5.4.1 or 5.2.1, 12 of the 14 files differ in line breaks. The proofs themselves
  check with any build of Rocq 9.3.0.
- `scripts/check_rocq.sh` (what `@rocq` runs) and `scripts/recheck.sh` find the Rocq
  themselves (`scripts/find_rocq.sh`): they try every `rocq` on the `PATH`, then the `rocq` of
  every opam switch, then `/opt/homebrew/bin/rocq` and `/usr/local/bin/rocq`, and take the first
  Rocq 9.3.0 that has a compiled Stdlib. `check_rocq.sh` prefers one built with OCaml 5.5, which
  the byte comparison needs, and warns if it has to use another. Each skipped candidate is
  reported with the reason, for example an opam Rocq without `rocq-stdlib`.
- `ROCQ=/path/to/rocq` overrides the search, and the scripts stop if that `rocq` is unusable.
  Prefer it over reordering the `PATH`: putting another installation first on the `PATH` can
  also replace the OCaml compiler that Dune uses. `check_rocq.sh` prints the Rocq version and
  the Stdlib directory it uses.

## The flambda release build

Measured binaries are built with OCaml 5.5.2 + flambda, Dune's release profile and `-O3`. The
release profile drops `-opaque`, so small functions inline across modules; a compiler without
flambda accepts `-O3` and ignores it. `-unsafe` is never used, because it would also remove the
bounds checks in the kernel check.

```sh
opam switch create 5.5.2+flambda ocaml-variants.5.5.2+options ocaml-option-flambda --no-switch
opam install --switch=5.5.2+flambda dune
opam exec --switch=5.5.2+flambda -- ocamlopt -config-var flambda   # prints true
opam exec --switch=5.5.2+flambda -- make release
```

`make release` builds the five binaries, `bench/schema/schema_bench.exe` and the benchmark
executables in `_build/default`. The dev profile (`dune build`) and the release profile share
`_build/default`, so switching between them rebuilds.

The default search reads a work clock that counts allocated words, so a dev build and a
release build of the same commit can schedule the single-worker time share and the schema probe
lane differently. Compare searches only between binaries built the same way; see
[development.md](development.md#checking-that-a-change-keeps-the-search).

## Editor setup

VS Code with the OCaml Platform extension and VsRocq works with the files in `.vscode/`.

- OCaml: Merlin and OCaml LSP read only build artifacts made by their own compiler.
  `dune-workspace.editor` adds an editor context built with the opam switch named `default`
  next to the normal build; select it with `DUNE_WORKSPACE=dune-workspace.editor` or
  `--workspace dune-workspace.editor` from the repository root. `.vscode/settings.json` sets
  this variable for the language server (`ocaml.server.extraEnv`); this setting has not yet been
  tried in VS Code itself. To use another switch, change it in both files.
- Rocq: `.vscode/settings.json` starts VsRocq through
  [scripts/rocq-editor.py](../scripts/rocq-editor.py), which first builds the Rocq files for the
  editor in `_build/rocq-editor`. Run `make rocq-editor` to do this by hand. The script uses the
  opam switch named by `AXIOM_FUZZER_ROCQ_SWITCH`, else opam's active switch, else the tools on
  the `PATH`; if there is no compiled Stdlib, it compiles one from the sources in
  `AXIOM_FUZZER_STDLIB_SOURCE` (a directory that contains `Lists/List.v`).

## Troubleshooting

| Symptom | Cause and fix |
| --- | --- |
| `The selected switch default is not installed`, or `Program opam not found`, from every `dune` command | `DUNE_WORKSPACE` selects `dune-workspace.editor` on a machine without an opam switch named `default`. Unset it, or change the switch in that file |
| `@rocq` stops with `Rocq: no usable Rocq 9.3.0 with its Stdlib was found` | No candidate on the `PATH`, in the opam switches or in Homebrew is Rocq 9.3.0 with a compiled Stdlib (the skipped ones are listed above the message); install `rocq-core` and `rocq-stdlib`, or point `ROCQ` at a Rocq that has its Stdlib |
| `@rocq` fails at a `cmp` of an extracted file | The Rocq was built with another OCaml than 5.5.x; the extraction differs in line breaks. The proofs are not affected |
| Benchmark tests fail with a `tarfile` error | Python older than 3.12 (for example macOS's `/usr/bin/python3` 3.9) |
| `axiom-replay` refuses a certificate it wrote itself | Certificates over 32 MiB exceed the reader limit; the solver warns when it writes one |
| `axiom-replay` rejects a certificate from another version | Certificates are not versioned; regenerate them with the matching version |
