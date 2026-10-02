# Sparse Nonattacking Chess Placements

**Every fixed asymptotic order and growth-index inversion (OEIS A201513
kings, A201540 knights; A201511 wazirs, A201861 ferses)**

A research report dated 2 October 2026, built from one manuscript. Its
author line is empty; the delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 03 | `Sparse_Chess_Asymptotics.zip` (wrapper directory `Sparse_Chess_Asymptotics/`), arrival commit `096ee7b87`; main file `Sparse_Chess_Asymptotics.tex`, now `article.tex` | none: no ProveIt commit is named; the manuscript describes an unpinned "targeted check of the current relevant ProveIt catalog" | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor
a tool), unrefereed, not formalized. Exact finite and symbolic checks
corroborate the arithmetic; the all-`n` statements rest on the written
proofs (Sections 3–5).

## What it proves

`K_n` and `N_n` count `n`-element subsets of the `n × n` board with no
two squares attacking by a king, respectively a knight move (no
one-per-row condition; rotations and reflections distinct).

- **Theorem 1.** Rational relative expansions to every fixed order against
  the carrier `B_n = e^{-9/2} n^{2n}/n!` (Kotěšovec's leading equivalent):
  `K_n/B_n = 1 + 7/(3n) + 119/(9n²) + 11327/(810n³) + 90475/(1944n⁴) + O(n⁻⁵)`,
  `N_n/B_n = 1 + 37/(3n) + 914/(9n²) + 330917/(810n³) + 966583/(1944n⁴) + O(n⁻⁵)`,
  with the ratio `N_n/K_n` and the logarithmic forms (all re-derived from
  the two series at intake, exact rational arithmetic).
- **Theorem 2 (any fixed finite symmetric move set `S`).**
  `a(n,n) = (n^{2n}/n!) e^{α_2} (Σ c_r n^{-r} + O(n^{-M-1}))`, `α_2 =
  -(|S|+1)/2`, and uniformly for `k/n` in a compact positive interval; the
  first correction is `c_1 = B + 1/3 - τ` (boundary loss `B`, triangle
  density `τ`), which is why kings and knights share the leading term but
  not the next one.
- **Connected-support polynomials (Section 3)**, a zero-free disk for the
  independence polynomial (Lemma 1), and an exact finite extraction formula
  (Proposition 1); quadratic cluster coefficients through `j = 6`; first two
  density corrections; the wazir and fers coefficients through order 4.
- **Section 7 (inversion).** A Lambert-`W` growth-index inverse with its
  first corrections, and a two-ceiling bracket of the integer threshold
  with the rounding qualification.

## What is not claimed

Kept from the manuscript and its package:

- The leading equivalent `B_n` is Kotěšovec's (OEIS, 29 November 2011; his
  book *Non-attacking Chess Pieces*, 6th ed., pp. 77, 293, 685–686); "It is
  not a new result of this report." The canonical cluster-expansion method
  is credited to Davies–Jenssen–Perkins and Pulvirenti–Tsagkarogiannis; "We
  do not claim a new general cluster method, or exhaustive historical
  priority for each specialized coefficient."
- The literature and catalogue checks are "a bounded source check, not proof
  of absence from all literature". No convergent infinite series or
  beyond-all-orders completion; no uniformity as `θ = k/n → 0` or `∞`; the
  smooth model "does not define combinatorial counts on noninteger boards";
  no unconditional rounding of the threshold.
- `compute_clusters.py --order J` makes "no practical claim … about
  arbitrarily high J"; the C++ row-DP is "a finite verification program,
  not an arbitrary-size counting API".
- **Carrier convention.** Coefficients depend on the carrier. The `c_r`
  above are relative to `B_n` with `n!` exact (first corrections `7/3`,
  `37/3`); relative to the Stirling-expanded carrier
  `e^{-9/2}(en)^n/sqrt(2πn)` the first corrections are `9/4`, `49/4`, and the
  `d_1` of the inverse section's logarithmic model are those numbers
  (`d_1 = c_1 - 1/12`). A dated note in Section 1 spells out the three
  carriers and the false readings.
- **The inversion is an instance of repository results, with no novelty
  claimed for the method.** Its core `x(log x + 1) = log y`,
  `x = L/W(eL)`, is `p0:prop:factorial-core` (`κ = 1`, `d = 1`) of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
  equivalently `t2:eq:unbalanced-core` (`κ = λ = 1`) of
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`
  (not the linear–logarithmic `p0:thm:lambert-core`: the phase is
  factorial); its first correction is the first two terms of
  `p0:prop:operator-form` (checked by hand at intake); the bracket is the
  separation condition, part (2) of `p0:thm:staircase`; part (1) does not
  apply. A dated `[write]` note at the end of Section 7 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic staircase arithmetic named
in the Section 7 note is formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
those lemmas concern an arbitrary monotone function.

**Repository search.** The manuscript's own ProveIt check (its last
section and `SOURCES.md`) is unpinned and bounded. The intake's untruncated
search of the collection, the transseries volumes, `Oeis/` and
`docs/reports/` for A201513, A201540, A201511, A201861 and for non-attacking
placements is the authoritative one; it found no overlap.

**Neighbouring reports.** None shares a result. The batch-77 report
`oeis-sequence-asymptotics/a227578-ordered-rook-paths` counts lattice paths
of rook *moves*; `a330266-balanced-smirnov-poisson` uses rook polynomials
(non-attacking rook placements). Neither concerns kings or knights.

## Notation

`B_n` (carrier) vs `B` (boundary loss); `d = |S|` vs the inverse-model
coefficients `d_j`; `a = α_2 = -9/2` vs the counts `a(n,k)`; `D = t d/dt`
vs the slope `D = log x + 2`; `N_n` (knights) vs the threshold `N(y)`;
`w(T)`, `h(T)` vs `w_j(T)`, `h_ℓ`; `J` an interval and a truncation order;
`A`, `H`, `L`, `x`, `y` two ways each. A table in the Section 1 `[write]`
note fixes each, with the false readings. No symbol was renamed.

## Labels

Every label carries the prefix `scp:`. The manuscript's 35 labels were
prefixed before anything cited them (34 `\ref`/`\eqref` targets updated),
and six section labels `scp:sec:…` were added: 41 labels in all. The
writing step also added three dated `[write]` notes (Section 1: provenance
and repository search, three carriers, the rook distinction, notation
table; Section 6: the files in the collection; Section 7: the instance
note), two bibliography entries (`scp-tai`, `scp-cti`), and set the
bibliography ragged-right. No statement, proof, number or table of the
manuscript was changed.

## Files

```text
README.md                                            this guide (replaces the delivery README)
PROOF.md                                             delivered Markdown version of the core mathematics (as delivered; no [write] notes)
SOURCES.md                                           delivered sources and scope of the literature check (as delivered)
independent_verification-README.md                   delivered README of the independent checks (independent_verification/README.md)
article.tex                                          the report (delivered as Sparse_Chess_Asymptotics.tex)
article.pdf                                          compiled report, 10 pages
code/compute_clusters.py                             connected-support enumeration; writes cluster_coefficients.json in the current directory
code/derive_expansion.py                             exact extraction formula; reads/writes JSON in the current directory
code/verify_finite.py                                direct 3x3-5x5 board enumeration, 12 checks (stdout; imports compute_clusters)
code/independent_verification-check_coefficients.py  111 row-DP comparisons and an independent Touchard extraction (independent_verification/check_coefficients.py)
code/independent_verification-row_dp.cpp            C++17 row-mask counter (independent_verification/row_dp.cpp); not compiled at intake
code/replay.sh                                       the delivered replay (delivered layout only)
code/build.sh                                        the delivered PDF build (expects Sparse_Chess_Asymptotics.tex beside it)
data/cluster_coefficients.json                       quadratic cluster polynomials through j = 6, four pieces
data/asymptotic_coefficients.json                    c_0..c_4 for kings, knights, wazirs, ferses
data/finite_verification.txt                         recorded verify_finite.py output
data/independent_verification-check_results.json     recorded check_coefficients.py result (independent_verification/check_results.json)
data/independent_verification-row_dp_counts.txt      frozen row-DP output, boards n <= 13 (independent_verification/row_dp_counts.txt)
data/requirements.txt                                sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement moved the package-root scripts to
`code/` and its outputs and `requirements.txt` to `data/`, and flattened
`independent_verification/` into names with the prefix
`independent_verification-` (README at the root, program files in `code/`,
outputs in `data/`). Not shipped: the delivered nine-page PDF
`Sparse_Chess_Asymptotics.pdf` and `SHA256SUMS` (a checksum ledger,
verified 19/19 at placement). Both survive in the archive:
`git show 096ee7b87:docs/incoming/Sparse_Chess_Asymptotics.zip > <scratch>/Sparse_Chess_Asymptotics.zip`.
No delivered file was excluded for size (the largest is `PROOF.md`,
14.5 KB).

Delivered text that names the delivery layout or unshipped files:
`code/replay.sh` (runs `compute_clusters.py`, `derive_expansion.py`,
`verify_finite.py` and `independent_verification/check_coefficients.py`
from its own directory, with `python`); `code/build.sh`
(`Sparse_Chess_Asymptotics.tex`/`.pdf`); `code/independent_verification-check_coefficients.py`
(reads `cluster_coefficients.json` from the parent of its directory and
`row_dp_counts.txt` beside itself, and writes `check_results.json` beside
itself); `independent_verification-README.md` (paths under
`independent_verification/`, `/tmp/chess_row_dp`); `PROOF.md`
(`compute_clusters.py` without a directory); `SOURCES.md` (the unpinned
"ProveIt catalog" search);
and the article's Section 6 (file names without directories; a dated note
there gives the collection layout).

## Rerun the checks (on a copy with the delivered layout)

The scripts write in the current directory and beside themselves, so never
run them here. From this directory (Git Bash; the scripts call `python`, so
put a SymPy-pinned interpreter first on `PATH`; on Windows they write CRLF):

```sh
R=$(mktemp -d) && mkdir "$R/independent_verification"
cp code/compute_clusters.py code/derive_expansion.py code/verify_finite.py code/replay.sh "$R/"
cp code/independent_verification-check_coefficients.py "$R/independent_verification/check_coefficients.py"
cp data/independent_verification-row_dp_counts.txt "$R/independent_verification/row_dp_counts.txt"
uv venv "$R/.v" && uv pip install -p "$R/.v" sympy==1.14.0
cd "$R" && PATH="$R/.v/Scripts:$R/.v/bin:$PATH" PYTHONUTF8=1 bash replay.sh
D="$OLDPWD/data"
diff -q --strip-trailing-cr cluster_coefficients.json "$D/cluster_coefficients.json"
diff -q --strip-trailing-cr asymptotic_coefficients.json "$D/asymptotic_coefficients.json"
diff -q --strip-trailing-cr finite_verification.txt "$D/finite_verification.txt"
diff -q --strip-trailing-cr independent_verification/check_results.json "$D/independent_verification-check_results.json"
```

At intake (2 October 2026, pinned SymPy 1.14.0, on a heavily loaded
machine, on a copy of the delivered layout) `compute_clusters.py --order 6`
and `derive_expansion.py` took under three minutes together, `verify_finite.py`
20 s and the independent check 6 s; all twelve finite-board checks and all
111 row-DP comparisons passed, the independent Touchard route reproduced
`7/3, 119/9, 11327/810, 90475/1944` and the knight row, and all four
regenerated outputs equal the shipped files up to line endings. The C++
row-DP regeneration (`independent_verification-README.md`) was not run.

## Build the PDF

pdfLaTeX with lmodern, amsmath, amssymb, amsthm, mathtools, booktabs,
geometry, hyperref and microtype. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 10 pages,
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source builds to 9 pages with the same clean log.)
`code/build.sh` is kept as delivered; to use it, copy it to a scratch
directory together with `article.tex` renamed to
`Sparse_Chess_Asymptotics.tex`.

## Provenance

- OEIS A201513, A201540, A201511, A201861 (accessed 2 October 2026);
  Kotěšovec, *Non-attacking Chess Pieces*, 6th ed. (2013); Davies–Jenssen–
  Perkins, arXiv:2004.06695v2; Pulvirenti–Tsagkarogiannis, Comm. Math.
  Phys. 316 (2012). Details in `SOURCES.md`.
- Repository input: an unpinned catalogue search only; no pin.
- Batch 77 of `docs/incoming`, manuscript 03 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
