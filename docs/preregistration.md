# Held-out corpus and TEST split: pre-registration

This page fixes, before the next evaluation, the held-out corpus that axiom-fuzzer will be
evaluated on and the rule that splits it. The manifest is
[benchmarks/corpora/heldout-tptp10.json](../benchmarks/corpora/heldout-tptp10.json): case names,
TPTP header facts and SHA-256 hashes, with no problem text.

**The TEST split has not been evaluated on 0.1.0, nor on any build after 2026-11-15.** It was
run twice before that date; see [History](#history-of-the-split).

## The corpus

- **Source**: TPTP v10.0.0, `TPTP-v10.0.0.tgz` with SHA-256
  `f23c2cb84c501f2c9441a4c056111d4db9a1e07dc74421760563ff0e2917499e`.
- **Eligible problems**: untyped FOF and CNF problems that axiom-fuzzer can parse, without a
  `conjecture` role, at most 1 MiB after preparation. Families of the frozen development corpus
  are excluded (the manifest lists their keys), and at most one problem per family (the first six
  characters of the name: domain and number) is taken.
- **Strata**: by TPTP rating, R0 [0, 0.1), R1 [0.1, 0.35), R2 [0.35, 0.65), R3 [0.65, 1], separately
  for the SET domain and the other domains, plus 24 satisfiable problems. The sample was drawn with
  seed 20261114 and the quotas in the manifest: 320 cases, 293 CNF and 27 FOF.
- **Preparation**: every `include` line is replaced by the complete included axiom file, with no
  other change: formula text, order, names and roles stay as they are, and no conjecture or status
  is transformed. The manifest records the SHA-256 of every source file and of every prepared
  file. Prepared files are modified TPTP files, so they are not distributed; rebuild them from the
  TPTP distribution and compare the hashes.

## The split rule

Within each stratum, sort the cases by the lowercase hexadecimal SHA-256 of
`"split-20261114:" + case`. Cases at even positions (0, 2, 4, ...) form the development split
**DEV**, cases at odd positions form **TEST**. The manifest records the split of every case, and
applying the rule to the manifest reproduces it.

| Split | UNSAT | SAT | Total |
| --- | --- | --- | --- |
| DEV | 149 | 12 | 161 |
| TEST | 147 | 12 | 159 |

## History of the split

- **2026-11-14**: the corpus and the split were built. From then on, DEV was the development
  split: the design and adoption decisions of every later phase used it, so results on DEV are
  optimistic.
- **2026-11-14 and 2026-11-15**: TEST was run twice, to confirm the first adoption on main. The
  first run compared main of that day with the integration of the first work items at 10 s with
  one worker and at 30 s with four workers (and experimental configurations that called external
  provers as oracles, which were never adopted). The second run compared main with the adoption
  build at 30 s with four workers: 87 and 106 of the 147 UNSAT cases. TEST was not used for
  tuning. These builds predate phases 3 to 9, and the runs are not reproducible from this
  repository (they used frozen binaries and drivers of the private evidence archive).
- **After 2026-11-15**: TEST was reserved and not run. The evaluation tooling refused any input
  that contained a TEST case name, and no TEST case name appears elsewhere in the repository.

The decisions confirmed on TEST in 2026-11 (the balanced worker rule, the process portfolio, the
footprint memory budget, the schema probe lane) are part of 0.1.0. A TEST result of 0.1.0 is
therefore held out from every later decision, but not from those.

## Plan for the next evaluation

The next evaluation on TEST follows [benchmarks.md](benchmarks.md) and reports:

- the release build of a tagged version, with every `UNSAT` re-checked by a separate
  `axiom-replay` against the prepared file;
- the default command line with one worker at 10 s and with four workers at 30 s, three seeds
  (503, 607, 701), each case decided by the majority of its seeds;
- the number of TEST UNSAT cases solved, the cases solved, and every alarm (any `UNSAT` on the 12
  satisfiable cases, any rejected or unverified certificate);
- the results header, the raw rows, and this manifest's SHA-256.

Any other comparison is reported as exploratory.

## TEST cases

| Stratum | Cases |
| --- | --- |
| nonSET/R0 (55) | ALG159+1, ANA009-2, ANA043-2, BOO007-4, BOO025-1, CAT011-1, COL116-2, COM004-1, COM009-2, FLD006-1, GEO022-3, GEO056-3, GRP019-1, GRP538-1, HEN008-1, HEN009-3, HWC003-1, HWV018-1, HWV020-1, KRS064+1, KRS072+1, KRS121+1, LCL069-1, LCL172-3, LDA001-1, LDA007-3, MGT007-1, NLP258-1, NUM004-1, PLA017-1, PLA022-1, PUZ008-3, PUZ016-2.005, REL003-1, REL048-1, RNG013-6, RNG038-1, RNG040-1, SCT052-1, SCT094-1, SCT100-1, SWB011+2, SWB019+1, SWB030+2, SWC086-1, SWC411-1, SWV325-2, SWW417-1, SWW421-1, SWX207-1, SYN483-1, SYO633-1, SYO745+1, TOP051-1, TOP053-1 |
| nonSET/R1 (35) | ALG395-1, ALG404-1, ANA020-1, BOO075-1, CAT004-3, COL064-1, COL124-1, FLD005-3, FLD034-1, GEO011-1, GRA117-1, GRA120-1, HEN011-5, HWV009-4, KLE084-10, KRS013-1, KRS089+1, LCL759-1, LCL809-1, LDA004-1, MGT021-1, MSC007-2.005, NLP149-1, NUN135-1.006, PLA011-2, PUZ005-1, ROB023-1, SWB031+2, SWC032-1, SWV286-1, SWV421-1.200, SWW399-1, SWW400-1, SYN122-1, SYO680-1 |
| nonSET/R2 (20) | COL121-1, COM005-1, CSR034-10, CSR072-10, FLD051-4, GRA146-1, GRA148-1, GRP765-1, LAT196-1, LCL430-1, MGT035-2, MSC024-1, NUN133-1, PLA037-1, PUZ062-2, REL019-1, RNG025-7, SCT040-1, SWW442-1, SYO594-1 |
| nonSET/R3 (10) | ALG408-1, COL096-1, GEO119-1, GRP719-1, KLE157-10, NUN092+1, PUZ056-10.020, SWC056-1, SWX194-1, SYO622-1 |
| SET/R0 (12) | SET005-1, SET006-1, SET012-4, SET024-3, SET065-6, SET787-1, SET825-2, SET833-2, SET838-2, SET848-2, SET849-2, SET859-2 |
| SET/R1 (7) | SET004-1, SET011-1, SET022-3, SET050-6, SET062-6, SET071-7, SET857-2 |
| SET/R2 (5) | SET097-7, SET134-6, SET147-6, SET195-6, SET860-2 |
| SET/R3 (3) | SET015-3, SET171-6, SET262-6 |
| SAT (12) | ANA006-1, COL069-1, GEO162-1, HWC004-1, KLE179+1, MSC009-1, NUM097-1, NUN090+1, REL053+1, SET461-6, SWV538-1.007, SWW673+1 |

The TPTP problems themselves are under the TPTP terms of use; see
[THIRD-PARTY.md](../THIRD-PARTY.md).
