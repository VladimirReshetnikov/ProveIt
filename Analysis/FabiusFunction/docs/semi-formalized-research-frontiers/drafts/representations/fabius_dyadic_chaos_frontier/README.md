# Dyadic Sensitivity and Polynomial-Chaos Frontiers for the Fabius--Rvachev Law

This archive is the reproducible source package for a repository-aware
research report on a new orthogonal-chaos layer of the Fabius/Rvachev random
series.

## Main files

- `fabius_dyadic_chaos_frontiers.tex` - complete self-contained LaTeX source.
- `fabius_dyadic_chaos_frontiers.pdf` - compiled A4 report.
- `LEAN_CROSSWALK.md` - label-complete map from all 40 nonconjectural paper
  results to the current Lean corpus, with exact remaining proof obligations.
- `experiments.py` - deterministic, extensively commented exact and
  high-precision experiment driver.
- `requirements.txt` - Python dependencies.
- `data/` - generated CSV tables and the human-readable numerical summary.
- `figures/` - vector PDF and raster PNG versions of every generated figure.
- `audit/CORPUS_AUDIT.md` - recursive repository audit and nonduplication
  boundary.
- `audit/SOURCE_AUDIT.md` - source/literature roles and proof boundary.
- `audit/POST_INTAKE_REVIEW.md` - repository-side mathematical corrections,
  reproducibility replay, and formalization boundary.
- `audit/corpus_manifest_2026-08-27.txt` - preserved recursive TeX path ledger.
- `SHA256SUMS` - integrity hashes for all other files in the archive.

## Mathematical contribution map

The report starts from the established representation

```text
X = sum_{j>=1} 2^{-j} V_j,      V_j iid Uniform[-1,1],
M(t) = E exp(tX) = product_{j>=1} sinh(t/2^j)/(t/2^j).
```

It develops and proves:

1. exact Hoeffding/functional-ANOVA components of `exp(tX)`;
2. an independent Bernoulli active-digit law whose probabilities are
   `p(x)=1-tanh(x)/x`, giving every variance share and Sobol index;
3. a marked tensor-Legendre law with modified spherical-Bessel degree marks;
4. a general smooth-observable interaction bound with the exact dyadic
   q-Pochhammer factor;
5. sharp top-order formulas for monomials and finite Bell--Bernoulli component
   expressions;
6. a small-field Gaussian-q-binomial interaction law and its first correction;
7. a Mellin-derived logarithmic-periodic effective-dimension asymptotic;
8. a quantitative total-variation phase limit for the centered interaction
   order;
9. an exact transfer between the no-active atom and the negative Fabius Laplace
   product;
10. a Thue--Morse mixed-difference corner and a Lambert-W tensor-degree cutoff.

Conjectures and future directions cover phase-mode uniqueness, strict
log-concavity, differential transcendence, the full geometric-q phase diagram,
inverse-Fabius chaos, automatic signs, best N-term approximation, and Lean
formalization.

The novelty convention is repository-relative and is documented in `audit/`.
Classical ingredients are explicitly separated from new deductions.

## Proof-status convention

The colored `P`, `I`, `C`, and `N` symbols in the report classify the
human-readable manuscript: `P` means proved in the report and `I` means
imported into the report. They are **not Lean status markers**.

`LEAN_CROSSWALK.md` audits all 40 labeled
theorem/proposition/lemma/corollary statements. The maintained report now
contains four deliberately statement-exact, compiler-backed results: the
totalized activation dictionary, the sharp local quadratic coefficient, the
geometric activation-dimension proposition, and the certified dyadic
prefix/tail corollary. The remaining status counts are 12 Unformalized, 21
Partial, and 3 Near-complete.

Two older compound statements have improved without becoming Complete.
`lem:p-bounds` is Partial because all its order and global quadratic bounds,
including sharpness of the coefficient `1/3`, are formalized, while its Taylor
expansion through `O(x^10)` is not. `prop:mu-refinement` is Partial because its
dyadic and geometric definitions, summability, refinements, positivity,
prefix decompositions, and tail estimates are formalized, while its Bernoulli
power series and radius statements are not.

`FabiusFunction.HyperbolicActivation` has an exhaustive public surface of four
definitions and 57 theorems; `FabiusFunction.ActivationAsymptotics` adds the
exact punctured limit proving quadratic sharpness; and
`FabiusFunction.GeometricActivationDimension` has two definitions and 29
theorems. The first two modules are real-valued: they do not identify their
totalized `realSinhc` with the separate complex sinc APIs. The geometric module
proves a uniform, nondegenerate convergence theory under `|q|<1`. Outside that
range no general summability is promised and the definition retains Mathlib's
totalized real-`tsum` semantics, although degenerate parameters may still give
a convergent series. Its negative-`q` results are algebraic and are not claims
about the report's geometric-uniform probability law, which assumes `0<q<1`.

For `thm:TM-corner`, Lean now contains the exact Boolean-cube, polynomial,
dyadic-sign, and report-grid clauses over a more general algebraic target. The
repeated `C^N` integral identity and one final report-shaped wrapper remain.

## Reproduce the numerical files

From the archive root:

```bash
python experiments.py --root .
```

The program makes no network requests and uses no Monte Carlo sampling. It
regenerates every file under `data/` and `figures/`. Infinite products and sums
use explicit tail bounds; the chosen precision and checks are recorded in
`data/numerical_summary.txt`.

Minimum supported environment:

- Python 3.11 or newer;
- `mpmath>=1.3`;
- `numpy>=2.0`;
- `scipy>=1.13`;
- `matplotlib>=3.8`.

The supplied outputs were regenerated with Python 3.13.5, mpmath 1.3.0, NumPy
2.3.5, SciPy 1.17.0, and Matplotlib 3.10.8.

The repository-side review replayed the experiment twice on 2026-08-30: once
with exactly those recorded versions and once with the then-current compatible
versions. Both runs exited successfully and generated the complete ten-data-
file, twelve-figure-file payload. After normalizing line endings, seven of ten
data files were byte-identical to the archive in both runs. The two Legendre
tables differed only by floating-point evaluation drift, while the numerical
summary changed only in the corresponding last-bit Parseval residual. Under
the recorded versions, the largest probability difference was `1.45e-15`,
and the largest Parseval quantity difference was `8.89e-16`. The six
regenerated plots were visually indistinguishable from the archived plots.
Thus the mathematical numerics reproduce to displayed precision, although
renderer metadata and last-bit floating results are intentionally not claimed
to be byte-reproducible across machines.

## Compile the report

A current TeX Live installation is sufficient. From the archive root, run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_dyadic_chaos_frontiers.tex
```

Equivalently, run `pdflatex` repeatedly until the table of contents and cross
references stabilize. The repository-side release PDF was rebuilt with three
explicit `pdflatex` passes using MiKTeX-pdfTeX 4.26 (pdfTeX 1.40.29);
`latexmk` was not available in that environment. Standard packages are used,
with Libertinus fonts when available and Latin Modern as a fallback.

## Verification status

- All theorem, equation, figure, and bibliography references resolve.
- The final PDF has 39 A4 pages. Every font is embedded and no Type 3 font is
  present in either the report or its six vector figures.
- The final PDF was preflighted and rendered page-by-page at 120 dpi. Four
  complete contact sheets were inspected, followed by full-resolution checks
  of the new totalized-activation, sharp-coefficient, geometric-dimension, and
  certified-tail pages, including the tail proof across its page break.
- No clipping, overlapping text, broken glyphs, or black rendering artifacts
  were observed.
- The experiment was replayed in two fresh trees. The six archived figure pairs
  were regenerated from the recorded environment after selecting TrueType
  output for the vector plots; the numerical data were retained where the
  replay audit found only the documented last-bit platform drift.

## Integrity check

From the archive root:

```bash
sha256sum -c SHA256SUMS
```

The active ledger contains exactly 32 entries - every package file except
`SHA256SUMS` itself - and verifies against the repository-normalized bytes.
