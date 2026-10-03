# Unitary Divisor Sum Colored Partitions and Their Asymptotics

**The recorded OEIS equivalents of A301981 and A301982 are false; an
unconditional `o(n^(1/3))` logarithmic law that cannot be `O(n^(1/4-ε))`, a
sequence-specific criterion equivalent to the Riemann hypothesis, a corrected
equivalent at an explicit point, all-fixed-order exact-saddle and off-center
expansions, and integer-threshold brackets**

A research report dated 2 October 2026, built from one manuscript. Its
author line reads only "Research article and reproducibility companion"; the
delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 70 (cluster P4) | `unitary-partition-report.zip` (wrapper directory `unitary-partition-report/`), arrival commit `096ee7b87`; main file `unitary-partitions.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor a
tool), unrefereed, not formalized. The proofs are analytic; the shipped
programs check finite exact arithmetic and floating-point diagnostics only.

## What it proves

`b_m = σ*(m)` is the sum of the unitary divisors of `m` (OEIS A034448).
A301981 is `∏(1-z^m)^(-b_m)` and A301982 is `∏(1+z^m)^(b_m)`; write `a_n^±`
for their coefficients, `A_- = π²/6`, `A_+ = π²/8`,
`c_± = 3(A_±/4)^(1/3)`, `t_0 = (2A_±/n)^(1/3)`.

- **Theorem 3.3 (refutation).** Kotěšovec's conjectured equivalents
  `a_n^± ~ m_n^±` recorded in the two OEIS entries (2018, inspected
  2 October 2026) are false; more strongly, `a_n^±/m_n^±` does not
  eventually stay in any compact subinterval of `(0, ∞)`. The proof is a
  least-height zeta-zero noncancellation (Lemma 3.1: the Mellin kernel,
  with denominator `ζ(2s-1)`, has a genuine pole with `3/4 ≤ ℜ s_0 < 1`)
  combined with an Abelian transfer (Lemma 3.2).
- **Theorems 6.1, 7.2 (unconditional logarithmic law).**
  `log a_n^± = c_± n^(2/3) + o(n^(1/3))`, and for no `0 < ε < 1/4` is the
  error `O(n^(1/4-ε))`.
- **Theorem 7.4 (RH criterion).** For each sign separately, RH holds if and
  only if `log a_n^± = c_± n^(2/3) + O_ε(n^(1/4+ε))` for every `ε > 0`.
  This is an equivalence: it neither proves nor disproves RH.
- **Theorem 6.1 (corrected equivalent at an explicit point).**
  `a_n ~ t_0^2 (12πA)^(-1/2) exp(f(t_0) + n t_0) = m_n exp(R(t_0))`, with
  relative error `o(1)` and no rate.
- **Theorem 5.2 (all fixed orders at the exact saddle)** with explicit
  cumulant corrections `C_j(t_n)` and error `O_M(t_n^(2M+2))`;
  **Theorem 9.1 (all fixed orders at the explicit point)** with Hermite
  grades that keep the mean mismatch and all odd grades.
- **Theorems 8.2, 9.2 (inverses).** Eventual increase of `a_n^±`; the integer
  threshold `N(y) = min{n : a_n ≥ y}` lies between two ceilings
  `⌈x_M(y) ∓ ε_M(y)⌉` with `ε_M = O(x_M^(-(2M+1)/3))`; `N(y) ~ (log y / c)^(3/2)`.

## What is not claimed

- RH is not proved or disproved; RH is assumed only in Lemma 7.3 and the
  direction "RH ⇒ bound" of Theorem 7.4. Every other result is
  unconditional. No simplicity of zeta zeros, no numerical zero location and
  no zero-residue expansion is used.
- The refutation does not say which one-sided divergence occurs (Remark
  after Theorem 3.3); no two-sided oscillation theorem is claimed.
- The explicit-point equivalent has no rate (Remark 6.2).
- The inverse constants `C_M`, `Y_M` are existence constants, not certified
  cutoffs; there is no exact single-ceiling identity `N(y) = ⌈x_M(y)⌉`
  (Remark 8.3).
- Priority: the Dirichlet series of `σ*` is classical (Tóth, unnumbered in
  §4.9 on p. 28, not his eq. (50)); Bureaux–Enriquez, Bodini et al., Dong et
  al., Bridges et al. and others receive explicit methodological credit; "a
  targeted literature search … not an exhaustive priority claim or a claim of
  a new general Mellin/RH method".
- Numerical checks: exact integer arithmetic for coefficients and exact
  rational tail majorants, but floating evaluations, root-finder results and
  ratios are **not** interval enclosures; a larger-cutoff, higher-precision
  match checks stability only. Finite numerics cannot establish a pure
  equivalent or decide RH.
- The five closing questions (Section 11) remain open: an explicit rate,
  effective constants, oscillation, zero-residue corrections, other weights.
- **Inversion: no novelty for the integer step.** The model inverted is the
  exact-saddle model `G_M` (or the explicit-point `L_M`), which keeps the
  arithmetic fluctuations; the Lambert-core theorems `p0:thm:lambert-core` /
  `p0:thm:lambert-centered` do **not** apply to it as stated. They apply
  only to the refuted pure models (`X = x^(2/3)`, `a = c_±`, `b_+ = -1`,
  `b_- = -5/4`, branch `W_{-1}`), whose inverse cannot locate `N(y)` within
  bounded distance. The width `ε_M` is the residual-to-root conversion
  `p0:thm:backward-error`, and the two-ceiling bracket is
  `p0:thm:staircase` (1)–(2) with `x_* = x_M(y)`, `η = ε_M(y)`; all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note after Remark 8.3 says so.

## Relation to the repository

**Claims about OEIS text, not about ProveIt.** Theorem 3.3 is the
manuscript's theorem about formulas printed in OEIS A301981 and A301982. At
intake, untruncated searches of the research-report collection, the
transseries volumes, `Oeis/` and `docs/reports/` for A301981 and A301982
returned no file, so no repository claim is refuted and nothing was
retracted. The delivery does not say that a correction was submitted to the
OEIS, and this report implies none.

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic order-theoretic steps named
in the inverse note are formalized for an arbitrary monotone function, not
for `a_n`: `Fabius.staircase_ceil` and `Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, and
`Fabius.abs_sub_right_inverse_le_div` in
`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`.

**Neighbouring reports.** The collection's other partition-product reports
(`a033552-catalan-partitions`, `a022629-distinct-partition-norms`,
`a097356-sqrt-restricted-partitions`,
`a238016-restricted-partitions-cubic-boundary`) and the batch-77 reports
`a174065-radix-layer-partitions` (where a pure OEIS equivalent likewise
omits an oscillating factor, there a log-periodic one) and
`a372395-acyclic-orientation-partitions` treat other products; none treats
unitary-divisor weights, a zeta-zero denominator or an RH criterion, and no
result is shared. (Pointers made here only; those reports are not edited.)

## Notation

The manuscript reuses letters: `c` (growth constant) vs the contour abscissa
`c_*`; the correction terms `C_j(t)` vs the constants `C_1, C_2`, `C_r`,
`C_M`; `K` four ways; `δ` three ways; `ε = ±1` in the cumulant recursion
(where `ε = 1` is the *minus* product) vs the small exponent `ε`; `H`
(holomorphic remainder) vs Hermite `H_d`; `σ(m)` vs a contour abscissa `σ`;
`N(y)` vs `N = ⌊1/t⌋`; `t_0` is the explicit point `(2A/n)^(1/3)`, not `t_x`
at `x = 0`; `R_±` is an exact (unbounded) remainder. A table in the first
`[write]` note (end of §1.1) fixes every such symbol. No symbol was renamed.

## Labels

Every label carries the prefix `udp:`. The manuscript's 79 labels were
prefixed before anything cited them (79 `\ref`/`\eqref` updated), and three
section labels were added (`udp:sec:results`, `udp:sec:prior`,
`udp:sec:questions`): 82 labels in all. The writing step also added four
dated `[write]` notes (end of §1.1: provenance, OEIS-facing claims, the RH
equivalence, neighbours, notation table; after Remark 8.3: the inverse note;
end of §10.3: the shipped files; end of §11: the open questions), one
bibliography entry (`udp-tai`), and restored the diacritic in "Kotěšovec"
(three places, printed "Kotesovec" in the delivery). No statement, proof or
number of the manuscript was changed.

## Files

```text
README.md                                 this guide (replaces the delivery README)
article.tex                               the report (delivered as unitary-partitions.tex)
article.pdf                               compiled report, 20 pages
code/numerics_core.py                     shared numerical core (mpmath); keep it beside the check scripts
code/check_oeis_prefixes.py               unitary-divisor enumeration and binomial products vs the OEIS prefixes (reads data/oeis-prefixes.json)
code/check_unitary.py                     integer recurrence through 1000, trial-divisor checks, principal residue, old-model diagnostics
code/check_saddle.py                      exact-cumulant centered formulas, M = 0, 1, 2
code/check_fixed_saddle.py                explicit-point equivalent and stationary-exponent comparisons
code/check_cutoff_precision.py            cutoff 1000/60 digits vs 2000/80 digits; WRITES two files into ../data
code/check_inverse.py                     centered model inverse tests
code/check_offcenter.py                   binomial products vs recurrence through 500, Hermite grades, odd-grade deletion
code/check_offcenter_replay.py            cutoff 1200/70 digits vs 1800/90 digits; WRITES two files into ../data
code/check_offcenter_inverse.py           explicit-point inverse checks
code/compare_replay.py                    JSON comparison of a replay directory with a reference directory
code/verify_manifest.py                   checks a delivered SHA-256 manifest (the manifests are not shipped)
code/safe_extract.py                      standalone safe ZIP extractor
code/package_release.py                   the delivery's release packer (do not run; see below)
code/reproduce.sh                         the delivered replay driver (expects the delivery layout; see below)
code/build.sh                             the delivered PDF build (expects unitary-partitions.tex; see below)
data/oeis-prefixes.json                   inspected OEIS prefixes (36 terms of A301981, 37 of A301982)
data/unitary_diagnostics.json             recorded check_unitary.py output
data/saddle_diagnostics.json              recorded check_saddle.py output
data/fixed_saddle_diagnostics.json        recorded check_fixed_saddle.py output
data/fixed_saddle_replay_2000_80.json     high-precision replay written by check_cutoff_precision.py
data/cutoff_precision_report.json         comparison report written by check_cutoff_precision.py
data/cutoff-precision-summary.json        recorded check_cutoff_precision.py output (rational tail bounds)
data/inverse_diagnostics.json             recorded check_inverse.py output
data/offcenter_diagnostics.json           recorded check_offcenter.py output
data/offcenter_replay_1800_90.json        high-precision replay written by check_offcenter_replay.py
data/offcenter_replay_report.json         comparison report written by check_offcenter_replay.py
data/offcenter-replay-summary.json        recorded check_offcenter_replay.py output
data/offcenter_inverse_diagnostics.json   recorded check_offcenter_inverse.py output
data/runtime-versions.json                reference environment (Python 3.12.14, mpmath 1.3.0)
data/requirements.txt                     mpmath==1.3.0
data/receipts-build-environment.txt       delivered receipt: pdfTeX, Python and mpmath versions
data/receipts-numerical-verification.json delivered receipt: entry points, case counts, source hashes
data/receipts-safe-extraction-tests.json  delivered receipt: safe_extract.py tests
data/receipts-visual-qa.json              delivered receipt: rendering checks of the delivered PDF
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed `unitary-partitions.tex` to
`article.tex`; moved `build.sh` and `reproduce.sh` from the package root to
`code/`, `requirements.txt` to `data/`, and `receipts/<name>` to
`data/receipts-<name>`. Not shipped: the delivered 18-page PDF
`unitary-partitions.pdf` and the checksum ledgers `MANIFEST.sha256` (39/39)
and `SOURCE-MANIFEST.sha256` (33/33), both verified at placement. All survive
in the archive:
`git show 096ee7b87:docs/incoming/unitary-partition-report.zip > <scratch>/unitary-partition-report.zip`.

Delivered text that names the delivery layout or unshipped files:
`code/reproduce.sh` (runs from its own directory; needs
`SOURCE-MANIFEST.sha256`, `unitary-partitions.pdf` and `build.sh` beside it,
and `pdftotext`); `code/build.sh` (compiles `unitary-partitions.tex` in its
own directory, writing `.build/`); `code/package_release.py` (writes
`SOURCE-MANIFEST.sha256` and `MANIFEST.sha256` into the directory above
`code/` and a ZIP beside that directory: run in place it would write into
this report and into `oeis-sequence-asymptotics/`); the receipts (delivery
paths `receipts/…` and hashes of the delivered files); and the article's
Section 10 (the "companion archive" with its manifests; a dated note there
says what is shipped).

## Rerun the checks (on a scratch copy)

Never run the scripts in this directory: `check_cutoff_precision.py` and
`check_offcenter_replay.py` overwrite four shipped files in `data/`. Also,
`compare_replay.py` compares every `*.json` of its reference directory, and
the shipped `data/` holds three `receipts-*.json` that no script produces, so
compare against a reference copy without them. Git Bash, from this
directory:

```sh
R=$(mktemp -d) && cp -R code data "$R" && cd "$R"
mkdir ref && cp data/*.json ref/ && rm ref/receipts-*.json
export PYTHONUTF8=1
PY="uv run --no-project --with mpmath==1.3.0 python"
run() { echo "$1"; $PY code/$1.py > data/$2.json; }
run check_oeis_prefixes oeis-prefix-check
run check_unitary unitary_diagnostics
run check_saddle saddle_diagnostics
run check_fixed_saddle fixed_saddle_diagnostics
run check_cutoff_precision cutoff-precision-summary
run check_inverse inverse_diagnostics
run check_offcenter offcenter_diagnostics
run check_offcenter_replay offcenter-replay-summary
run check_offcenter_inverse offcenter_inverse_diagnostics
$PY code/compare_replay.py ref data
```

This is the sequence of `code/reproduce.sh` without its manifest check and
its PDF rebuild. The comparison is of parsed JSON, so Windows line endings do
not matter. Alternatively use the delivered layout: extract the archive
above and run `bash reproduce.sh` there (it also rebuilds and compares the
PDF text, which depends on the TeX installation).

At intake (2 October 2026, Python 3.13.5, mpmath 1.3.0, a heavily loaded
machine, a three-minute limit per step) the manifest check passed (33
files), and twelve recomputed JSON files equalled the recorded ones;
`check_inverse.py` and `check_offcenter_inverse.py` did not finish within
the limit, so `inverse_diagnostics.json` and
`offcenter_inverse_diagnostics.json` were not regenerated, and the PDF
rebuild was not run. Expect the whole sequence to take more than ten
minutes.

## Build the PDF

pdfLaTeX with lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, longtable, microtype, hyperref and enumitem. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 20 pages, no
errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source builds to 18 pages, also without warnings.)
`code/build.sh` is kept as delivered; to use it, copy it to a scratch
directory together with `article.tex` renamed to `unitary-partitions.tex`.

## Provenance

- OEIS A301981, A301982 (entries by V. Kotěšovec, 30 March 2018), A034448;
  Tóth, J. Integer Seq. 20 (2017), Art. 17.2.1; Bureaux–Enriquez, Discrete
  Analysis 2016:19; Bodini–Duchon–Jacquot–Mutafchiev (DGCI 2013); Dong–
  Robles–Zaharescu–Zeindler, arXiv:2412.20101; Bridges–Brindle–Bringmann–
  Franke, Math. Ann. 390 (2024); Trudgian, Funct. Approx. 52 (2015); see the
  article's bibliography.
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 70 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
