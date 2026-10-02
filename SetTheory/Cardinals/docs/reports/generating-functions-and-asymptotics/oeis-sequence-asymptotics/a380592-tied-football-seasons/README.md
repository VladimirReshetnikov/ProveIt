# Asymptotic Enumeration of Tied Football Seasons

**A leading equivalent with a three-residue theta factor, every fixed
order via Isaev's complex cumulant theorem, the first correction, a
discrete-Gaussian conditional score law, and residue-aware inverse
thresholds (OEIS A380592)**

A research report dated 2 October 2026, built from one manuscript. Its
author line is empty, the PDF metadata has an empty Author field, and the
delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 67 | `tied-football-report.zip` (wrapper directory `tied-football-release/`), arrival commit `096ee7b87`; main file `report/tied-football-asymptotics.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor
a tool), unrefereed, not formalized. The replay checks the finite algebra
(exact rationals, symbolic identities, exact counts for `n ≤ 4`); the
analytic estimates are proved in the text, not by the programs.

## What it proves

`a(n)` (A380592: 1, 3, 27, 1083, 296081, …) counts seasons of a double
round-robin league of `n` labeled teams, two distinguished matches per
pair, 3/1/0 scoring, in which every team finishes with the same score;
`M = n(n-1)` matches.

- **Theorem 1.1 (leading equivalent).** `a(n) ~ B_n Θ(c_n)` with
  `B_n = 3^M n^(-1/2) (9/(56πn))^((n-1)/2) e^(-9829/65856)`,
  `c_n = 8(n-1)/3 - 13/84`, and the positive 1-periodic theta function
  `Θ(c) = Σ_j e^(-4π²j²/9) e^(2πijc)`; the multiplier depends on `n mod 3`
  and cannot be replaced by 1. Proof: mean-matching exponential tilts, a
  sharp global Fourier localization (a negative quartic gives an exact
  Gaussian majorant; a separate outlier bound handles its complement,
  Lemma 3.1), the local integral with the common-score shift `-13/84`
  (Section 4) and dominated summation over all common scores (Section 5).
- **Proposition 5.1.** The conditioned common score converges, on each
  residue class, to a discrete Gaussian centred at `c_n`, with all fixed
  moments; the centre is not the conditional mean.
- **Theorem 1.2 (every fixed order).** `a(n) = B_n (Σ_{j≤R} H_j(c_n) n^(-j)
  + O_R(n^(-R-1)))` with `H_j` finite rational combinations of derivatives
  of `Θ`, after checking the mixed-difference hypotheses of Isaev's complex
  cumulant theorem (Section 6), with a finite exact Gaussian-moment
  algorithm; the first correction `R_{n mod 3}` from the explicit polynomial
  `Q(δ)` (Section 7).
- **Proposition 8.1 (inverse).** Smooth inverses `ν_{R,r}` of the
  residue-class forward expansions and eventual residue-aware ceiling
  enclosures for `N(L) = min{n : a(n) ≥ e^L}`.

## What is not claimed

- The model and its exact finite enumeration belong to Jehn–Habermann–Lavrov
  (arXiv:2503.14509); values for `n = 5…8` are taken from that paper and the
  OEIS, not recomputed.
- No new general local-limit or cumulant theorem: Isaev's complex theorem
  (arXiv:2508.16952, Theorem 1.2) is the external input; Barvinok–Hartigan,
  Isaev–McKay and Isaev–McKay–Zhang are credited precedents.
- Every **fixed** order only: no convergence of the series, no uniformity
  for an order growing with `n`, no effective remainder constants, no
  certified small-`n` range; the decimals of the residue table are
  diagnostics, not interval enclosures.
- The inverse enclosures are eventual theoretical bounds with non-effective
  constants and onset; near the residue lattice no floor-free formula
  resolves the rounding.
- The bounded literature search (2 October 2026) "is not an exhaustive
  novelty certificate".
- The programs implement the stated coefficient checks, not an optimized
  arbitrary-order engine; the integration-by-parts program does not supply
  the complete second correction.
- **The inversion uses repository results, with no novelty claimed for the
  method.** Its dominant block is quadratic (`b t²`, `b = log 3`), so the
  Lambert cores `p0:thm:lambert-core`, `p0:prop:factorial-core` and the
  reversion `p0:thm:lambert-centered` of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  do **not** apply (the seed is `√(L/b)`, no Lambert function occurs). The
  phase is an admissible core (`p0:def:core`) and the successive
  substitution is the reversion about it, `p0:thm:core-reversion` (CTI
  `t2:prop:scaled` in
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`).
  The residue-aware enclosure combines the residue-class formula, part (4)
  of `p0:thm:staircase`, with the separation condition, part (2), applied
  in each class. A dated `[write]` note at the end of Section 8 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt result. The arithmetic of the two staircase
parts named in the Section 8 note is formalized as
`Fabius.staircase_separation` and `Fabius.isLeast_residue_class` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
those lemmas concern arbitrary reals and monotone functions, not `a(n)`.

**Neighbouring reports.** The intake's untruncated repository search found
no other report on A380592 or tied seasons. The batch-77 report
`oeis-sequence-asymptotics/a000571-tournament-score-sequences`
(manuscript 68, cluster P3) treats tournament score sequences from their
exact generating function: a different model and method, and neither
report uses the other. No reciprocal note was made there.

## Notation

Symbols are printed as delivered. A table in the first `[write]` note
(Section 1) fixes the letters with two or more meanings (`Q`/`Q_0`,
`R`/`R_r`, `B_n`/`B`/`b_3`/`B_4`, `b`, `d`, `D`, `c`/`c_n`, `K`/`K_0`,
`Θ`/`θ`, `v`, `u`/`U`, `M`/`M_j`, `L`/`L_r`, `H_j`/`H_3`, `x`, `h`), with
the false reading that matters most: the theta centre `c_n` is not the
conditional mean of the common score. No symbol was renamed.

## Labels

Every label carries the prefix `tfs:`. The manuscript's 72 labels were
prefixed before anything cited them (55 `\ref`/`\eqref` updated), and the
label `tfs:sec:model` was added to Section 1: 73 labels in all. The writing
step also added three dated `[write]` notes (Section 1: provenance,
neighbour, notation table; end of Section 8: the relation to the
transseries volumes; Section 10: the shipped layout), two bibliography
entries (`tfs-tai`, `tfs-cti`), and set the bibliography ragged-right. No
statement, proof or number of the manuscript was changed.

## Files

```text
README.md                                         this guide (replaces the delivery README)
article.tex                                       the report (delivered as report/tied-football-asymptotics.tex)
article.pdf                                       compiled report, 17 pages
code/replay.py                                    the delivered one-command replay (expects code/ and expected/ beside it; see below)
code/leading_term_checks.py                       one-match cumulants, 135 symmetric-polynomial identities, leading constants, exact enumeration n = 1..4
code/symbolic_identity_checks.py                  general-q quartic, aggregated cubic and quartic, completed-square constants
code/first_correction_checks.py                   exact power-sum Gaussian pairings for the first-correction moments
code/cumulant_filtration_checks.py                alternative set-partition aggregation of moments and cumulants through order six
code/finite_n_gaussian_checks.py                  exact Gaussian-cumulant evaluations at n = 20, 50, 100, 1000
code/independent_ibp_checks.py                    Gaussian integration-by-parts cross-check of the first correction
code/residue_constants_checks.py                  theta factors, first corrections, conditional means and variances per residue
code/gaussian_moments.py                          shared finite-moment helper
code/output_support.py                            shared output helper (default output: replay_outputs/ beside code/)
code/build-report.sh                              the delivered PDF build (expects report/tied-football-asymptotics.tex)
data/expected-leading_term_checks.json            frozen fixture of leading_term_checks.py
data/expected-symbolic_identity_checks.json       frozen fixture of symbolic_identity_checks.py
data/expected-first_correction_checks.json        frozen fixture of first_correction_checks.py
data/expected-cumulant_filtration_checks.json     frozen fixture of cumulant_filtration_checks.py
data/expected-finite_n_gaussian_checks.json       frozen fixture of finite_n_gaussian_checks.py
data/expected-independent_ibp_checks.json         frozen fixture of independent_ibp_checks.py
data/expected-residue_constants_checks.json       frozen fixture of residue_constants_checks.py
data/requirements.txt                             sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed
`report/tied-football-asymptotics.tex` to `article.tex`, moved
`replay.py` and `build-report.sh` to `code/`, `requirements.txt` to
`data/`, and `expected/<name>.json` to `data/expected-<name>.json`. Not
shipped: the delivered 15-page A4 PDF `tied-football-asymptotics.pdf` and
`MANIFEST.sha256` (a checksum ledger, verified 22/22 at placement and
retired). Both survive in the archive:
`git show 096ee7b87:docs/incoming/tied-football-report.zip > <scratch>/tied-football-report.zip`.

Delivered text that names the delivery layout or unshipped files: the
delivery README (replaced by this guide: `python replay.py` and
`bash build-report.sh` from the package root, `sha256sum -c
MANIFEST.sha256`); the article's Section 10 (a package with the PDF and a
SHA256 manifest; `python replay.py` from its root); `code/replay.py`
(reads `code/<name>.py` and `expected/<name>.json` relative to its own
directory, so in `code/` it finds neither; its default output,
`code/replay_outputs/`, is refused by `output_support.py` as lying inside
`code/`); `code/output_support.py` (a check script run
directly writes to `replay_outputs/` in this report directory unless
`TIED_FOOTBALL_OUTPUT_DIR` is set); `code/build-report.sh` (compiles
`report/tied-football-asymptotics.tex` and copies the PDF to the package
root). A dated note in Section 10 says so.

## Rerun the checks (on a scratch copy)

Rebuild the delivered layout from the shipped files in a scratch directory
(Git Bash, from this directory):

```sh
R=$(mktemp -d) && cp -r code "$R/" && cp code/replay.py "$R/" && mkdir "$R/expected"
for f in data/expected-*.json; do b=$(basename "$f"); cp "$f" "$R/expected/${b#expected-}"; done
cd "$R" && PYTHONUTF8=1 uv run --no-project --with sympy==1.14.0 python replay.py --output-dir "$R/out"
```

`replay.py` compares every result with its frozen fixture (exact for
integers, rationals, polynomials and decimal strings; relative tolerance
`5e-13` for binary floats) and never writes the fixtures. At writing
(2 October 2026, heavily loaded machine) it printed "PASS: all 7 checks
matched their frozen fixtures" after 401 s; at intake, run in the
delivered layout, the same result took 81 s. Alternatively use the
delivered layout itself:
`git show 096ee7b87:docs/incoming/tied-football-report.zip > x.zip`,
extract, and run `python replay.py` in `tied-football-release/`.

## Build the PDF

pdfLaTeX with fontenc, lmodern, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, microtype, hyperref and enumitem. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 17 A4
pages, no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. (The delivered source built to 15 pages with the same
clean log.) `code/build-report.sh` is kept as delivered; to use it, copy
it to a scratch directory with `article.tex` placed as
`report/tied-football-asymptotics.tex`.

## Provenance

- Jehn–Habermann–Lavrov, arXiv:2503.14509 (2025); OEIS A380592; Isaev,
  arXiv:2508.16952v2, Theorem 1.2; Barvinok–Hartigan, arXiv:0910.2497;
  Isaev–McKay–Zhang, J. Combin. Theory Ser. B 172 (2025); Isaev–McKay,
  Random Structures Algorithms 52 (2018) and arXiv:2508.18731.
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 67 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
