# Dyadic Sensitivity and Polynomial-Chaos Frontiers for the Fabius--Rvachev Law

This archive is the reproducible source package for a repository-aware
research report on a new orthogonal-chaos layer of the Fabius/Rvachev random
series.

## Main files

- `fabius_dyadic_chaos_frontiers.tex` - complete self-contained LaTeX source.
- `fabius_dyadic_chaos_frontiers.pdf` - compiled A4 report.
- `LEAN_CROSSWALK.md` - label-complete map from all 41 nonconjectural paper
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
- `SHA256SUMS.arrival.txt` - immutable submitted 30-entry ledger.
- `SHA256SUMS` - authoritative integrity hashes for every other current file.

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
11. an arbitrary-index square-summable activation theorem, including its
    global quadratic budget, exact Tannery limit, and sharp geometric and
    dyadic specializations.

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

`LEAN_CROSSWALK.md` audits all 41 labeled
theorem/proposition/lemma/corollary statements. The maintained report now
contains six statement-exact, compiler-backed results: the totalized
activation dictionary, the activation-bounds lemma including its finite Taylor
jet, the sharp local quadratic coefficient, the geometric
activation-dimension proposition, the certified dyadic prefix/tail corollary,
and the square-summable activation-series theorem. The remaining status counts
are 12 Unformalized, 20 Partial, and 3 Near-complete.

The older compound statement `lem:p-bounds` is now Complete.  The divided-slope
bridge is `Fabius.tanhDiv_eq_dslope`; the finite analytic calculation is
`Fabius.tanh_sub_taylor_nine_isBigO`; and the report's activation expansion is
formalized in the canonical norm-power form by
`Fabius.activationProbability_sub_taylor_eight_isBigO` and in the literal
`O(x^10)` form by
`Fabius.activationProbability_sub_taylor_eight_isBigO_pow`.
`prop:mu-refinement` remains Partial: its dyadic and geometric definitions,
summability, refinements, positivity, prefix decompositions, and tail estimates
are formalized, but its all-order Bernoulli power series, convergence-radius
statements, and active-count expectation bridge are not.

The current activation tranche is source-verified at commit
`a345425d21d90e680bf15e34093af42c69c08a83`. Its seven modules expose an
exhaustive public surface of 6 definitions and 99 theorems, or 105 public
declarations: `HyperbolicActivation` (4+58), `ActivationTaylor` (0+3),
`ActivationSeries` (0+3), `ActivationAsymptotics` (0+2),
`ActivationSeriesAsymptotics` (0+1), `GeometricActivationDimension` (2+30),
and `GeometricActivationAsymptotics` (0+2). The earlier `7c8d1f1...`
checkpoint remains a narrower historical milestone rather than the provenance
of these new results.

The generic series theorem permits an arbitrary index type and signed or zero
real weights, provided their squares are summable. Under that hypothesis its
activation series is genuinely summable; it is not an appeal to Mathlib's
totalized fallback `tsum`. All quotient limits are punctured at zero. The
geometric API proves a uniform, nondegenerate convergence theory under
`|q|<1`; negative-`q` statements are deterministic algebraic generalizations,
while the report's active-count probability interpretation assumes `0<q<1`.
No theorem identifies the deterministic dyadic sum with `E K_t`, and the
all-order Bernoulli series and radius theorems, active-count expectation
bridge, and q-binomial chaos coefficient remain outside this activation
milestone.  The proved finite Taylor jet does not imply any of those stronger
claims.

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
references stabilize. The current repository release PDF was rebuilt from a
clean source directory with exactly three explicit `pdflatex` passes using
pdfTeX 1.40.22 (TeX Live 2022/dev); `latexmk` was not used. Standard packages
are used, with Libertinus fonts when available and Latin Modern as a fallback.

## Verification status

- All theorem, equation, figure, and bibliography references resolve.
- The final PDF has 40 A4 pages and is an unencrypted 819,265-byte PDF 1.5
  artifact. Every font is embedded and no Type 3 font is
  present in either the report or its six vector figures.
- The final PDF was preflighted and all 40 pages were rendered at 120 dpi.
  Four complete contact sheets were inspected, followed by full-resolution
  checks of pages 12--13, 22--23, and 36--38: the scaled and square-summable
  limits, the geometric/dyadic sharp coefficients, the conclusion, status
  matrix, and formula atlas.
- No clipping, overlapping text, broken glyphs, or black rendering artifacts
  were observed.
- The exact five appended compiler-backed result headings audited during the
  PDF release are each extractable once when matched with their theorem number
  and class. The report SHA-256 is
  `0be7f0943e8d5fb795878aa0b3ecb21af25680155ad214ee2f1598de50e705ea`.
- The experiment was replayed in two fresh trees. The six archived figure pairs
  were regenerated from the recorded environment after selecting TrueType
  output for the vector plots; the numerical data were retained where the
  replay audit found only the documented last-bit platform drift.

## Integrity check

From the archive root:

```bash
sha256sum -c SHA256SUMS
```

The active ledger contains exactly 33 entries—every regular package file
except `SHA256SUMS` itself, including this README, the immutable arrival
ledger, the Lean crosswalk, and all four audit files---and verifies against the
repository-normalized bytes.

## Repository filing provenance

This package was filed on 2026-08-30 from
`drafts/incoming/fabius_dyadic_chaos_frontier.zip` (1,351,045 bytes;
SHA-256
`d57fd01c3991a6a7ecd6ba6e745729c745745d3265cb3cfd414aac1991b11b86`).
The archive was a safe single-wrapper delivery: it contained no absolute or
parent-traversal paths, symlinks, encrypted entries, duplicate paths, or
case-folding collisions, and its CRC check passed.  The submitted 30-entry
ledger verified 30/30 against the arrival bytes and is preserved unchanged as
`SHA256SUMS.arrival.txt` (SHA-256
`85c42740d869c520d5264049f945e52b3c9cfc1bc837a19aaf05c886c55aa6ea`).
Nine CSV files were then normalized from CRLF to the repository's required LF
line endings; `SHA256SUMS` is the authoritative current-package ledger.

After that intake checkpoint was published, the repository-side review
replayed the numerical program, repaired the six vector figures to remove
Type 3 fonts, corrected the manuscript's proof and status boundaries, added
the label-complete Lean crosswalk, and rebuilt the 40-page report in exactly
three explicit `pdflatex` passes. The details and remaining formalization
obligations are recorded in `audit/POST_INTAKE_REVIEW.md` and
`LEAN_CROSSWALK.md`.
