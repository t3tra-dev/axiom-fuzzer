# TPTP problems for evaluation

`tptp/` holds the original text of seven problems and five axiom files from **TPTP v9.0.0** and
one problem from **TPTP v6.4.0** (201,986 bytes in total). They are attributed to the TPTP Problem
Library: Copyright 1993 onwards, Geoff Sutcliffe and Christian Suttner. No program or library
of TPTP is included.

The [TPTP terms of use](https://seetptp.tptp.org/file/TPTPWorld/TPTP/Documents/ReadMe) allow the
redistribution of parts of the library in original form with attribution; redistributing modified
parts needs permission. Every file is stored unchanged, comments, formulas and order included, and
`manifest.json` records its source Git blob hash and its SHA-256. The texts come from a pinned
commit of a [TPTP v9.0.0 mirror](https://github.com/lammdachs/proofatlas-tptp-subset/tree/61e94d5f85e320a91ae7cdda8aca84d0bac5911d)
and from the [SWV851-1 file kept by E](https://github.com/eprover/eprover/blob/3ae362fd5096a515197d4468cf714aeb5f79607d/EXAMPLE_PROBLEMS/TPTP/SWV851-1.p).
The TPTP version is recorded per problem; these files are not an evaluation of the current TPTP
library as a whole.

| Problem | Task and reason for inclusion | Form and size¹ | Published status |
| --- | --- | --- | --- |
| SWV001-1 | Program verification PV1: a small verification condition with equality as a dedicated predicate | CNF, 14 clauses | UNSAT |
| SWV002-1 | Program verification E1: built-in equality and nested function terms | CNF, 23 clauses | UNSAT |
| HWV001-1 | Verifying a circuit that swaps two inputs without crossing wires; tests equational reasoning | CNF, 47 clauses | UNSAT |
| SWC078-1 | Matching a list-processing component's specification against a requirement; many library axioms | CNF, 199 clauses | UNSAT |
| KRS018+1 | A satisfiable knowledge base from OWL Lite; a control that detects false refutations | FOF, 4 formulas | SAT |
| KRS063+1 | An inconsistency from OWL's oneOf with inverseOf; quantifiers, equivalences and equality | FOF, 27 formulas | UNSAT |
| PLA012-1 | A plan that puts block D on B and B on C; state transitions and function terms | CNF, 31 clauses | UNSAT |
| SWV851-1 | Hoare logic with procedures from Isabelle/Sledgehammer: a larger input from a proof assistant, with deep function terms and equality | CNF, 669 clauses | UNSAT |

¹ After expanding every needed `include`; CNF counts include the negated conjecture. The name, the
source paper, the original purpose and the status stay in each file's header. The problems were
chosen for untyped first-order FOF/CNF that the parser handles, several application areas, with
and without equality, a satisfiable control and different input sizes. They were not exchanged
after seeing axiom-fuzzer's results, and they are not claimed to represent large modern
industrial problems.

The original headers of the two KRS problems note that the encoding of data types may be wrong.
What is evaluated is the published first-order formulas and their status, not OWL as a whole or
the original semantics of its data types. The note of SWV001-1 that its axioms are incomplete is
kept as well.

`benchmarks/corpus.py` checks the hashes of the original files, then replaces each
`include('Axioms/...').` with the whole axiom file in a temporary directory of the measurement
output. It removes, adds or reorders no formula and never negates a conjecture. Every prover gets
the same prepared bytes, and the output's manifest records the original files and the
transformation. The original comments stay in the input, but the expected status and rating are
never used to choose a solver, steer the search or stop it; the status is only compared with the
result afterwards.

The diagnostic certificate that this project rebuilt for SWV851-1 from an external prover's proof
and checked with its own primitive inferences is not part of the repository: it re-encodes clauses
of the problem, so, like the evidence archives of the design experiments, it is kept privately and
not distributed.
