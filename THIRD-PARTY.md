# Third-party material

The project's own code and documentation are released under the MIT licence ([LICENSE](LICENSE)).
This file describes the material that is under another licence, or that comes from or follows
other projects. [REUSE.toml](REUSE.toml) declares the copyright and licence of every path, and
[LICENSES/](LICENSES) holds the licence texts. No file carries a licence header.

| Material | Where | Licence |
| --- | --- | --- |
| Rocq Standard Library code in the extracted checkers | the 14 files of section 1 | LGPL-2.1-only |
| TPTP problems and axiom files, verbatim | `benchmarks/problems/tptp/`, `tests/fixtures/tptp/Problems/`, `tests/fixtures/tptp/Axioms/` | TPTP terms (`LicenseRef-TPTP`) |
| Strategies re-implemented from E and Vampire | the modules of section 3 | MIT, with the attributions of section 3 |
| Data: measurements and corpus manifests | `benchmarks/checker.csv`, `benchmarks/corpora/`, `benchmarks/results/` | CC-BY-4.0 |

## 1. Rocq Standard Library code in the extracted checkers

The proof checkers in these 14 files are OCaml that Rocq extracted from the Rocq development in
`rocq/`, as `rocq/Extraction.v` specifies. The files of release 0.1.0 are the extraction made with
Rocq 9.3.0 and rocq-stdlib 9.2.0 (the versions `axiom-fuzzer.opam` names for development):

- `lib/proof/avatar_checker.ml`, `lib/proof/avatar_checker.mli`
- `lib/proof/kernel_checker.ml`, `lib/proof/kernel_checker.mli`
- `lib/proof/natural_checker.ml`, `lib/proof/natural_checker.mli`
- `lib/proof/rocq_checker.ml`, `lib/proof/rocq_checker.mli`
- `lib/proof/wire_checker.ml`, `lib/proof/wire_checker.mli`
- `lib/proof/wire_normalizer.ml`, `lib/proof/wire_normalizer.mli`
- `lib/syntax/source_checker.ml`, `lib/syntax/source_checker.mli`

Besides the extraction of the project's own definitions, these files contain OCaml translations,
produced by extraction, of definitions from the Rocq Standard Library (Stdlib): the AVL and list
finite maps of `FSets.FMapAVL` (`Raw`, `IntMake`, `Make`) and `FSets.FMapList` (`Raw`), the ordered
types of `Structures.OrderedType` and `Structures.OrderedTypeEx` (`Nat_as_OT`, `PairOrderedType`),
`Structures.OrdersTac` (`MakeOrderTac`), the merge sort of `Sorting.Mergesort` (`Sort`),
`ZArith.Int` (`Z_as_Int`), the integer modules `Pos`, `N`, `Z` and `Nat` (`PArith.BinPos`,
`NArith.BinNat`, `ZArith.BinInt`, `Arith.PeanoNat`), and functions of `Lists.List` and
`Init.Datatypes`.

The Rocq Standard Library is copyright INRIA, CNRS and contributors and is distributed under the
GNU Lesser General Public License, version 2.1 ([LICENSES/LGPL-2.1-only.txt](LICENSES/LGPL-2.1-only.txt)).
Because the 14 files contain code translated from it, each of them is distributed under
LGPL-2.1-only as a whole. The rest of the project uses them as a library and keeps its own licence.

The files are generated and never edited by hand. The Rocq sources under `rocq/` are their
preferred form for modification: `dune build @rocq` (`scripts/check_rocq.sh`) extracts the files
again from these sources and requires the result to be byte-identical to the files in the
repository, so the sources of a release regenerate its files byte for byte. A change to the files
is a change of `rocq/` followed by a new extraction. For that reason they carry no notice inside;
this section and REUSE.toml are their notice.

Executables built from this repository contain these modules. Whoever distributes such executables
must meet section 6 of the LGPL-2.1, for example by making the complete source of this repository
available with them.

## 2. TPTP Problem Library

The TPTP (Thousands of Problems for Theorem Provers, <https://tptp.org>) is copyright 1993-onwards
by Geoff Sutcliffe and Christian Suttner. It has no open-source licence: its copyright notice
permits verbatim redistribution of parts of the TPTP that is clearly attributed to the TPTP, and
requires permission to distribute a modified part. Its conditions of use ask that results state
the TPTP release, name each problem unambiguously and note every change made to the formulae.
[LICENSES/LicenseRef-TPTP.txt](LICENSES/LicenseRef-TPTP.txt) quotes these sections of the TPTP
ReadMe.

The repository holds TPTP files only verbatim, each file byte-identical to its source, header and
comments included. It contains no modified TPTP material: where a test needs part of a problem, or
needs it changed, it reads the verbatim file and makes the change in memory at run time.

### 2.1 Benchmark problems

`benchmarks/problems/tptp/` holds 13 files of the TPTP, redistributed verbatim:

- from TPTP v9.0.0, through the mirror <https://github.com/lammdachs/proofatlas-tptp-subset> at
  commit `61e94d5f85e320a91ae7cdda8aca84d0bac5911d`: the problems HWV001-1, KRS018+1, KRS063+1,
  PLA012-1, SWC078-1, SWV001-1 and SWV002-1, and the axiom files HWC002-0, PLA001-0, PLA001-1,
  SWC001-0 and SWV001-0;
- from TPTP v6.4.0, as kept in E's repository (<https://github.com/eprover/eprover>, commit
  `3ae362fd5096a515197d4468cf714aeb5f79607d`): the problem SWV851-1.

`benchmarks/problems/manifest.json` records the git blob hash and the SHA-256 of each file, and
[benchmarks/problems/README.md](benchmarks/problems/README.md) describes the problems.
Benchmark runs expand the `include` directives (`benchmarks/corpus.py`) and write the expanded
inputs into their output directory (by default under `_build/`); the repository stores no expanded
copy.

### 2.2 Test fixtures

`tests/fixtures/tptp/` holds 11 files of TPTP v10.0.0, redistributed verbatim from the release
archive <https://tptp.org/TPTP/Distribution/TPTP-v10.0.0.tgz> (SHA-256
`f23c2cb84c501f2c9441a4c056111d4db9a1e07dc74421760563ff0e2917499e`), in the TPTP layout so that
include directives resolve: the problems `Problems/GRP/GRP001-1.p`, `Problems/PUZ/PUZ001-1.p`,
`Problems/BOO/BOO002-1.p`, `Problems/RNG/RNG019-7.p`, `Problems/HEN/HEN012-1.p` and
`Problems/REL/REL029-1.p`, and the axiom files `Axioms/GRP003-0.ax`, `Axioms/RNG003-0.ax`,
`Axioms/HEN001-0.ax`, `Axioms/REL001-0.ax` and `Axioms/SET004-0.ax`.
`tests/fixtures/tptp/manifest.json` records the release and the SHA-256 of each file, and
`tests/regression/tptp_fixtures_test.py` checks them.

The OCaml tests read these files with the library's TPTP reader (`tptp_problem` in
`tests/test_support.ml` expands the includes) and change them only in memory:

| Test | TPTP problem | Used in memory |
| --- | --- | --- |
| `tests/unit/e_golden_tests.ml` | GRP001-1 with `Axioms/GRP003-0.ax`; PUZ001-1 | the whole problems |
| `tests/unit/heuristic_tests.ml` (the BOO002-1 test) | BOO002-1 | the whole problem |
| `tests/unit/heuristic_tests.ml` (E's initial evaluation order) | RNG019-7 | 8 of the 15 clauses of its include `Axioms/RNG003-0.ax` |
| `tests/unit/heuristic_tests.ml` (the HEN012-1 test) | HEN012-1 with `Axioms/HEN001-0.ax` | the whole problem, the negated conjecture renamed `goal` |
| `tests/unit/heuristic_tests.ml` (E's creation order) | REL029-1 | 2 clauses of its include `Axioms/REL001-0.ax`, clausified |
| `tests/regression/unfold_tests.ml` (`ring`) | RNG019-7 | 4 clauses of `Axioms/RNG003-0.ax`, renamed, with 2 clauses written for the test |
| `tests/unit/vampire_tests.ml` (the Vampire slice members) | `Axioms/SET004-0.ax` | 4 clauses, renamed, with 3 clauses written for the test |

The E traces in `tests/unit/e_golden_tests.ml` (section 4) name each input clause by its name in
the problem, not by E's rendering of it.

### 2.3 Names and quotations

The documentation and comments name TPTP problems, axiom files and formula names. TPTP problems that the documentation names, other than those above, are not
part of this repository.

A diagnostic certificate that this project rebuilt for SWV851-1 re-encodes clauses of the problem;
like the evidence archives of the design experiments, it is kept privately and not distributed.

## 3. Strategies re-implemented from E and Vampire

Several modules re-implement search behaviour of two automated theorem provers, so that their
strategies can run inside this project's given-clause loop:

- **E 3.5.9** (<https://github.com/eprover/eprover>, tag `E-3.5.9`, commit
  `d71a93ad66f3f710c34c4223f14a6ef3d298f6a1`), by Stephan Schulz and the contributors listed in E's
  `DOC/CONTRIBUTORS`. E is licensed under both the GNU General Public License, version 2 or later,
  and the GNU Lesser General Public License, version 2.1 or later (E's `COPYING`).
- **Vampire 5.1.0** (<https://github.com/vprover/vampire>, release `v5.1.0`, commit
  `7b2f410ec4430c26217a85db62cf0c4a97042f8d`), copyright its authors and contributors and their
  institutional affiliations, under the Vampire licence, a modified BSD 3-Clause licence that is
  reproduced at the end of this section.

| Module | Re-implements |
| --- | --- |
| `lib/calculus/eselection.ml` | E's literal selection functions (`HEURISTICS/che_litselection.c`) |
| `lib/calculus/eorder.ml` | E's precedence and symbol-weight generation for KBO and LPO (`HEURISTICS/che_to_precgen.c`, `che_to_weightgen.c`) |
| `lib/calculus/unfold.ml` | E's unfolding of equational definitions (`CLAUSES/ccl_unfold_defs.c`) |
| `lib/saturation/evaluation.ml` | E's clause evaluation and priority functions (`HEURISTICS/che_*.c`) |
| `lib/saturation/e_initial.ml` | E's evaluation order of the initial clauses (`CONTROL/cco_proofproc.c`, `CLAUSES/ccl_clausefunc.c`) |
| `lib/saturation/e_genorder.ml` | E's creation order of a given clause's conclusions (`CONTROL/cco_proofproc.c`, `cco_paramodulation.c`) |
| `lib/saturation/e_simparamod.ml` | E's simultaneous paramodulation (`CLAUSES/ccl_paramod.c`) |
| `lib/calculus/vampire.ml` | Vampire's slice options, symbol precedence, KBO weights, preprocessing, literal selection and clause selection (`Shell/Options.cpp`, `Kernel/KBO.cpp`, `Kernel/LiteralSelector.cpp`, `Saturation/AWPassiveClauseContainers.cpp` and others it cites) |
| `lib/calculus/ordering.ml` (parts) | Vampire's literal order and literal selection functions (`Kernel/Ordering.cpp`, `Kernel/LiteralSelector.cpp`) |
| `lib/saturation/heuristic.ml` | E's heuristics and strategies, and Vampire's slices, as named members |

A few other modules (`lib/calculus/calculus.ml`, `lib/saturation/engine.ml`,
`lib/saturation/passive.ml`) cite the E or Vampire function that one of their functions
reproduces.

These modules are re-implementations, not translations. They are written in OCaml over this
project's own term, clause and proof types and reproduce the behaviour of the upstream provers, so
that a ported strategy makes the same choices as the original; unit tests compare them with traces
of E itself. No upstream source file was copied. A few short functions follow an upstream
definition step by step because they must reproduce an upstream order exactly, for example the
term and literal comparisons in `lib/saturation/e_initial.ml` (E's `TermStructWeightCompare` and
`EqnStructWeightCompare`). If a module were found to be a translation of E's source code, it would
be distributed under E's LGPL-2.1-or-later option, and REUSE.toml would declare that.

`lib/saturation/heuristic.ml` quotes some E heuristic definitions and E strategy names (from E's
`HEURISTICS/schedule.vars`), and nine Vampire 5.1.0 strategies ("slices") in Vampire's encoded
option format.

Every inference these strategies make is an ordinary certificate step, so they change which proofs
are found, never which proofs are accepted.

The Vampire licence (Vampire's `LICENCE`, version 5.1.0):

```text
Vampire licence - BSD 3-Clause

Vampire Software Licence Agreement
Copyright © 2020

Vampire is copyright (C) 2020 by
its authors and contributors (see AUTHORS) and their institutional
affiliations. All rights reserved.

The Vampire licence is a (modified) BSD 3-Clause licence.
This Vampire licence supersedes all previous licences covering usage of Vampire.


The source code of Vampire is open and available to students, researchers,
software companies, and everyone else to study, to modify, and to redistribute
original or modified versions; distribution is under the terms of the modified
BSD licence (reproduced below).

Note that some software included with Vampire is available under a more permissive licence.
For example, both Minisat and Z3 are used internally by Vampire.

In the below, this Software refers to Vampire in any form. 

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.


THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT OWNERS AND CONTRIBUTORS
''AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

## 4. Comparison provers (not distributed)

`benchmarks/external.py` (`make bench-external`) compares the search with three external provers.
It downloads them at run time into a temporary directory and never stores or bundles them:

- E (<https://github.com/eprover/eprover>): GPL-2.0-or-later or LGPL-2.1-or-later;
- Vampire (<https://github.com/vprover/vampire>): the Vampire licence (section 3);
- Zipperposition (<https://github.com/sneeuwballen/zipperposition>): BSD-2-Clause.

The repository contains no binary or source code of these provers. Some unit tests compare the
re-implementations of section 3 with values that E 3.5.9 printed (for example the clause
evaluations recorded in `tests/unit/e_golden_tests.ml`).

## 5. Build and check tools (not distributed)

Building and checking the project uses, but the repository does not include: the OCaml compiler,
whose runtime and standard library the executables link (LGPL-2.1-or-later with the OCaml static
linking exception); Rocq and rocq-stdlib (LGPL-2.1-only), which check the proofs and regenerate the
extracted checkers; and dune, ocamlformat and Python, which build, format and test the project.
