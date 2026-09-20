# The Six-State Shuffle Bound

**Three independent certificate computations, one finite-to-infinite theorem,
constructive reachability**
Research manuscript prepared for Vladimir Reshetnikov — 20 September 2026.


> **The certificate databases are not distributed.** `data/certificates.jsonl`,
> `data/certificates_masks.jsonl`, `data/certificates.txt` and
> `certificates/cores.cert` together came to about 6 MB and are regenerated
> deterministically by the routes below; database C's 453 records
> (`residual/`) and every worked example cited in the article are still
> shipped, so the article's displayed cases remain checkable as they stand.

## Result and scope

The manuscript gives a reproducible computer-assisted proof of the conjectured
worst-case shuffle state-complexity bound whenever `m,n >= 2` and
`min(m,n) <= 6`:

    F(m,n) = 2^(m*n-1)
             + 2^((m-1)*(n-1)) * (2^(m-1)-1) * (2^(n-1)-1).

In particular, for every `n >= 2`:

    F(6,n) = 63*2^(6*n-6) - 31*2^(5*n-5).

The alphabet is finite but allowed to depend on the two state counts. The
construction uses the full alphabet of pairs of transformations. The theorem
is not a fixed-small-alphabet result. It does not settle the unrestricted
conjecture for both dimensions at least seven.

The shared core theorem is proved exactly once, by a finite-to-infinite
induction on the lexicographic rank `(m+n,|S|)`. The **finite premise of that
induction is discharged three separate times**, from three certificate
databases that are not reducible to one another. Any one of the three is a
complete proof by itself.

A second result constructs a word reaching any valid target subset `S` from
any specified root, in three increasingly sharp forms:

| Form | Bound |
|---|---|
| dimension | `\|S\| + min(m,n) - 2` |
| support | `E + min(r,c) - 2`, with `r,c` the numbers of nonempty rows/columns |
| dual | `min{ 2(\|S\|-1), \|S\| + min(m,n) - 2 }` |

Four separate distinguishability arguments are given, one of them over a
**fixed three-letter alphabet**, which additionally shows that all `2^(mn)`
subsets are pairwise distinguishable whether or not they are reachable.

**Status:** This is an AI-assisted research draft with explicit mathematical
proofs and executed finite verification. It has not received independent human
peer review and has not been checked by a proof-assistant kernel. The range
extends the results expressly obtained in the primary sources located for this
project; a targeted literature search found no prior resolution of this strip,
but that negative result is not a proof of novelty and bibliographic priority
remains provisional. See `SOURCE_STATUS.md` and the manuscript's status and
trust-boundary sections.

## Provenance

This package is a merge of four independently prepared research packages on
the same conjecture. Each proved the shared theorem; they differ in *how*.

| Original package | How it proved the theorem |
|---|---|
| `shuffle-six-state-certificates` | database **A**: 10,642 spanning predecessor certificates over orbit-closure-checked representatives; SMT discovery; two-stage checker (Python local check exporting a verified-target list, then a C++ coverage enumeration consuming only that list). This package is the spine of the merged text. |
| `shuffle-six-state-strip` | the **same** database A by the same proof — its certificate file and this one agree in all 10,642 keys and all 10,642 witnesses, recomputed during the merge. Contributed the support-form word bound, a second serialization with a record-by-record agreement test, a single-binary C++ verifier, an iterative explicit-stack constructor, a 111,984-word regression suite, an undefined-behavior-sanitizer run, and a standalone literature audit. |
| `shuffle-six-state-theorem` | database **B**: an *independent* finite computation over a degree-sorted canonicalization proved to give exactly one representative per orbit; 10,619 witnesses, **none** of which coincides with database A's witness for the same target. Also the fixed three-letter distinguishability theorem. |
| `shuffle-six-state-complexity` | database **C**: a materially different proof adding a fifth analytic reduction (balanced-triple contraction) that shrinks the finite obligation to 453 certificates over widths at most 11, with a deterministic **solver-free** search whose regeneration was byte-identical. Also the dual word bound. |

## The three certificate databases

|  | Classified objects | Records | Widths | Discovery | File |
|---|---|---:|---:|---|---|
| **A** | hard matrices, orbit-closure coverage | 10,642 | ≤ 20 | SMT (Z3) | `data/certificates.jsonl` (+ two other encodings) — *regenerate, see below* |
| **B** | hard matrices, degree-sorted canonical | 10,619 | ≤ 20 | SMT (Z3) | `certificates/cores.cert` — *regenerate, see below* |
| **C** | residual cores (no balanced triple) | 453 | ≤ 11 | solver-free enumeration | `residual/certificates.tsv` |

Verified during the merge, directly from the shipped files:

- B's 10,619 target keys are a **strict subset** of A's 10,642. The 23 extra
  records of A are exactly the shapes with more rows than columns: twenty-one
  of shape 6×5, one 5×4, one 6×4. A certifies each hard matrix in the
  orientation in which it arises; B orients every target with `m <= n` and
  recovers the rest by transposition. Per row count, A stores
  1 / 5 / 63 / 10,573 records at 3 / 4 / 5 / 6 rows, against B's
  1 / 5 / 62 / 10,551. **Do not reconcile 10,642 and 10,619 into one number**
  — the difference is a real artifact of two different canonicalization
  conventions, one of which additionally proves its list minimal while the
  other proves only that its orbit closures cover.
- Of the 10,619 keys present in both, **zero** carry the same `(f,g,T)`.
- 8,117 of A's 10,642 row maps are **not** injective; all 10,619 of B's are
  permutations, while 10,113 of B's column maps are not; all 453 of C's
  records have both maps bijective.
- C shares only **2** target keys with A, and the same 2 with B.

SHA-256 digests:

    A  c44f2ebe73ac2584f1ff9d31cec7fc2e2560ab8fd166c80e86d80eb012c6b594
    B  e376820a4de82e1388ea67727ee96bb0cc1c7047d38dd4ae9cfae5617c45abd4
    C  6059c807de8aadbadfbdb363c805f83109395063fbbb6e5d87cad45c8b80a48f

This archive ships **no checksum manifest**, by design. A digest identifies
exact data; it is not a substitute for checking them.

## Read the article

Open `shuffle_six_state.pdf`. The complete LaTeX source is
`shuffle_six_state.tex`; keep the `tables` directory beside it when rebuilding.

Material kept alongside a parallel account of the same statement is marked in
the text with a numbered **parallel account** box saying what that variant
buys over the others.

## Verify the proof — four routes

None of the four needs Z3, a network connection, a Python package
installation, or a proof assistant.

### Route 1 — database A, two-stage (the default)

Requirements: Python 3.10+, Make, and a GCC- or Clang-compatible C++17
compiler (the checker uses `__builtin_ctzll` and population-count builtins).

```sh
make check
```

The successive stages are important:

1. `src/check_certificates.py` validates all 10,642 local witnesses and exports
   the checked target identifiers to `audit/verified_targets.tsv`.
2. `src/coverage.cpp` independently enumerates every antichain of nonempty
   proper column subsets, checks every hard target against the row-permutation
   orbits of the validated witnesses, and writes `audit/coverage.json`.
3. `src/test_suite.py` performs independent small-grid breadth-first checks,
   exhaustive and seeded target/word replays, an additional Python antichain
   enumeration through five rows, and malformed-certificate rejection tests.
4. `src/negative_coverage_test.py` deliberately omits the unique three-row
   certificate and confirms that exhaustive coverage fails on that omission.

The first check alone is not a coverage proof. The second check alone is not a
witness proof. Both must complete successfully, along with the mathematical
finite-to-infinite argument in the article.

Without Make:

```sh
python3 src/check_certificates.py
c++ -O3 -std=c++17 src/coverage.cpp -o audit/coverage
./audit/coverage audit/verified_targets.tsv > audit/coverage.json
python3 src/test_suite.py
python3 src/negative_coverage_test.py
```

### Route 2 — database A, one self-contained binary

```sh
g++ -O3 -std=c++17 -Wall -Wextra -pedantic src/verify_all.cpp -o verify_all
./verify_all data/certificates.txt
python3 src/test_artifacts.py ./verify_all
python3 src/test_construct_iterative.py
```

The final substantive line must be

    PASS: 7836132 labeled antichains enumerated; 5239572 hard antichains covered.

These totals span `m = 1..6` inclusive, so they exceed the `m >= 2` totals in
the table below; the one-row case contributes 3 antichains and no hard family.
Run `src/test_construct_iterative.py` **without** Python's `-O` flag: some of
its additional test conditions use the ordinary assertion mechanism.

`src/test_artifacts.py` compares `data/certificates.txt` and
`data/certificates_masks.jsonl` record by record — a cross-check of the
writers that only exists because both encodings are shipped.

*Known issue on this machine:* `verify_all` segfaults under MinGW/Windows on
the six-row traversal. This reproduces identically in the unmodified donor
package, so it is a platform issue, not a merge artifact; the recorded passing
run is in `logs/verification.txt`, with a sanitizer rerun in
`logs/verification_ubsan.txt`.

### Route 3 — database B, regenerating verifier

```sh
mkdir -p build
g++ -std=c++20 -O2 -Wall -Wextra -pedantic src/verify.cpp -o build/verify
./build/verify certificates/cores.cert
python3 tests/verify_certificates.py
python3 tests/test_construction.py
```

`build/verify` both validates the supplied triples and **regenerates the
entire canonical representative set**, comparing the full set of target keys
rather than record counts. Expected output ends with `OVERALL: PASS`. To
regenerate the enumeration tables independently of the certificate file:

```sh
g++ -std=c++20 -O2 src/enumerate_cores.cpp -o build/enumerate_cores
./build/enumerate_cores build/cores.csv build/core_counts.csv
```

and compare with the shipped `data/cores.csv` and `data/core_counts.csv`.

### Route 4 — database C, no compiler at all

```sh
cd residual
python3 verify.py --json verification.json
python3 test_construct.py
```

Python 3.9+ and its standard library suffice. The expected final message is

    PASS: certificates, exhaustive coverage, and auxiliary checks.

`--quick` checks certificate soundness only, omits exhaustive coverage, and
must not be represented as verification of the finite lemma. The certificate
file can also be regenerated deterministically, with **no solver**:

```sh
g++ -O3 -std=c++17 generate.cpp -o generate
./generate > regenerated.tsv 2> regenerated.log
python3 verify.py --certificates regenerated.tsv
```

In the recorded run that regeneration was byte-identical to the shipped file.

Check exit statuses; do not infer success merely from the presence of an output
file. Reports are overwritten when checks are rerun. Recorded elapsed times may
differ from the original audits.

### Expected exhaustive counts

Database A, two-stage accounting (`m >= 2`, degenerate singleton families
excluded):

| Rows | Antichains visited | Hard labeled families | Certificates |
|---:|---:|---:|---:|
| 2 | 4 | 0 | 0 |
| 3 | 18 | 1 | 1 |
| 4 | 166 | 15 | 5 |
| 5 | 7,579 | 1,957 | 63 |
| 6 | 7,828,352 | 5,237,599 | 10,573 |

Database A, single-binary accounting (`m >= 1`, degenerate families included):

| Rows | Stored | All labeled antichains | Hard antichains | Covered |
|---:|---:|---:|---:|---:|
| 1 | 0 | 3 | 0 | 0 |
| 2 | 0 | 6 | 0 | 0 |
| 3 | 1 | 20 | 1 | 1 |
| 4 | 5 | 168 | 15 | 15 |
| 5 | 63 | 7,581 | 1,957 | 1,957 |
| 6 | 10,573 | 7,828,354 | 5,237,599 | 5,237,599 |
| **Total** | **10,642** | **7,836,132** | **5,239,572** | **5,239,572** |

The two tables are two accountings of one traversal, not two computations.

Database B (oriented `m <= n`): 6 / 20 / 168 / 7,581 / 7,828,354 antichains
and 0 / 1 / 5 / 62 / 10,551 core orbits at 2..6 rows, totalling 10,619
representatives. `data/core_counts.csv` gives a four-way breakdown per `(m,n)`
— all antichains, labeled cores, degree-sorted survivors, orbits.

Database C (residual cores, oriented `m <= n`): 168,673 row-labeled column
families and 453 representatives, over `4x4`, `5x5..5x7` and `6x6..6x11` only;
every other case has none. The recursion visits 1 / 7 / 79 / 2,715 / 584,473
prefix nodes for `m = 2..6`.

Here columns form an unordered family; the row labels remain fixed. These are
not counts of all ordered rectangular matrices.

## Construct and replay a word — four constructors

```sh
python3 src/construct.py examples/six_by_seven_input.json \
  --output audit/replayed_example.json
```

Input format: `{"m":2,"n":3,"root":[0,0],"target":[[0,1],[1,0]]}`.
Rows and columns are numbered from zero. `root` is optional and defaults to
`[0,0]`. A valid target meets the root row and root column; it need not contain
the root cell. At least one dimension must be at most six.

| Constructor | What it buys |
|---|---|
| `src/construct.py` | JSON in, JSON out; pre-validates the target, replays the word and rechecks the length bound. Recursive: can hit Python's recursion limit on very wide grids. |
| `src/construct_iterative.py` | **explicit reduction stack** — logical recursion depth does not impose the interpreter's limit on the number of columns. Use this as the engine on wide targets. Same JSON shape with key `cells` instead of `target`. |
| `python/construct_word.py` | importable `Constructor` class, `construct(m,n,S,start=(0,0))`, plus `--start row,column`. Reads database B. |
| `residual/construct.py` | `--rows/--columns/--masks/--origin/--output`, zero masks allowed for empty columns, dynamic recursion-limit raising, and checks **both** branches of the dual length bound. The only one exercising the balanced-triple step. |

All four reject invalid targets and replay before reporting success.

The command-line constructors accept at most six **rows**. For a grid with at
most six columns instead, transpose the target, construct, then exchange the
two coordinate transformations in every letter; there is no automatic
transposition option.

Bundled examples:

| Example | Target cells | Constructed word length | Proved bound |
|---|---:|---:|---:|
| 6 by 7, target `(12,17,18,24,33,34,36)`, database A certificate | 14 | 11 | 18 |
| the same target, database B certificate | 14 | 10 | 18 |
| 6 by 7, target `(14,20,25,26,33,34,36)` | 17 | 16 | 21 |
| 6 by 7 residual core, target `(3,5,9,14,17,33,50)` | 16 | 17 | — |
| 6 by 20 (all 3-subsets of `[6]`), database A | 60 | 35 | 64 |
| the same, database B | 60 | 39 | 64 |
| 6 by 100 | 300 | 115 | 304 |

The two certificates for `(12,17,18,24,33,34,36)` are incompatible — one has a
non-injective row map, the other a permutation — which is the cleanest single
illustration that databases A and B are independent.

The 6-by-100 example repeats each three-element column type five times; ordinary
containment reductions handle the repetitions without any 100-column certificate.
It is the concrete demonstration that the finite classification is of
obstruction *types*, not of widths.

## Rebuild the PDF

```sh
make pdf
```

or `latexmk -pdf -interaction=nonstopmode shuffle_six_state.tex`. A TeX Live or
MiKTeX installation with the packages in the preamble is sufficient. The table
input files are already included; to regenerate the four data-derived ones:

```sh
python3 src/make_tables.py
make pdf
```

No external bibliography processor is needed. The PDF build uses New PX
text/math fonts installed in TeX; no font files are distributed here.

## Optional witness discovery

Not needed for proof checking. An installed Z3 shared library is needed only
for searching for fresh certificates for databases A and B; database C's
search needs no solver at all.

```sh
make enumerate
python3 src/search_certificates.py
```

The regenerated target list is written to `audit/enumerated_targets.tsv`; fresh
witnesses go to `audit/regenerated_certificates.jsonl`. The search refuses to
overwrite an existing output file. `Z3_LIBRARY` may name an explicit
shared-library path if automatic discovery fails. The original run used version
4.13.3.0 via Python's standard-library `ctypes`, without the `z3py` package.

A packaged parallel regeneration driver is also included:

```sh
python3 discovery/regenerate.py regenerated --jobs 4
./verify_all regenerated/certificates.txt
```

A regeneration run needs a fresh output directory. Different solver versions
may produce different witnesses; bytewise identity with the supplied database
is neither expected nor required on the SMT routes. Validate fresh witnesses
with the same independent stages:

```sh
python3 src/check_certificates.py audit/regenerated_certificates.jsonl \
  --targets-out audit/regenerated_targets.tsv \
  --report audit/regenerated_local_check.json
./audit/coverage audit/regenerated_targets.tsv > audit/regenerated_coverage.json
```

The optional finder for database B is `search/predecessor_search.py` with
`search/z3local.py`, supporting targeted rediscovery by family integer, e.g.
`--rows 6 --family 94506455040 --timeout-ms 10000`.

A search failure or timeout is not a counterexample to the original conjecture.

## Contents

| Path | Contents |
|---|---|
| `shuffle_six_state.tex`, `.pdf` | the merged manuscript and its source |
| `data/certificates.jsonl` | database A, coordinate-pair encoding |
| `data/certificates_masks.jsonl` | database A, column-mask encoding — *regenerate* |
| `data/certificates.txt` | database A, plain-integer encoding |
| `certificates/cores.cert` | database B, 10,619 records |
| `residual/certificates.tsv` | database C, 453 records |
| `data/cores.csv`, `data/core_counts.csv` | database B target keys and four-way counts |
| `data/strip_example_6x7*.json` | second worked 6×7 target and its 16-letter word |
| `data/theorem_example_6x7_word.json` | the 10-letter word from database B |
| `src/` | database A checkers, coverage, constructors, tests, target enumerator, Z3 interface |
| `src/verify.cpp`, `src/core_enumeration.hpp`, `src/enumerate_cores.cpp` | database B verifier, enumeration header, CSV generator |
| `src/verify_all.cpp`, `src/test_artifacts.py` | single-binary route for database A |
| `python/`, `tests/`, `search/` | database B constructor, independent checks, optional finder |
| `residual/` | database C: checker, solver-free generator, constructor, tests, logs |
| `discovery/` | packaged parallel regeneration driver for database A |
| `examples/` | human-checkable certificates, targets, replayable words |
| `audit/` | database A run reports, environment, search logs, target lists, regeneration smoke test |
| `audit/theorem/` | database B run reports, structured summary, larger test cases |
| `logs/` | single-binary route logs, sanitizer rerun, literature search audit |
| `tables/` | data-derived LaTeX table rows |
| `SOURCE_STATUS.md` | sources, attribution, and novelty limitations |

## Trust boundary

The solver is not trusted for correctness: every claimed witness is checked as
finite integer and set data. Database C's discovery path does not use a solver
at all. The Python and C++ checker implementations, compilers, runtimes, and
hardware are still trusted. No checker here is a proof-assistant kernel.

"Independent checker" means independent of the search and canonicalization
algorithms — and, across the three databases, independent of one another's
representative sets and witnesses. It does **not** mean independent human
authorship or independently maintained third-party software: every program here
was written during these investigations. Three databases agreeing is stronger
evidence than one, but they were prepared in the same environment, and that is
a residual common cause.

A later formalization must prove both the witness-checkers' soundness and the
coverage enumerations' completeness. Importing a record count — 10,642, 10,619
or 453 — as an axiom would not accomplish the coverage proof, which is the part
that matters.
