# Dyadic Sensitivity and Polynomial-Chaos Frontiers for the Fabius--Rvachev Law

This archive is the reproducible source package for a 34-page repository-aware
research report on a new orthogonal-chaos layer of the Fabius/Rvachev random
series.

## Main files

- `fabius_dyadic_chaos_frontiers.tex` - complete self-contained LaTeX source.
- `fabius_dyadic_chaos_frontiers.pdf` - compiled A4 report.
- `experiments.py` - deterministic, extensively commented exact and
  high-precision experiment driver.
- `requirements.txt` - Python dependencies.
- `data/` - generated CSV tables and the human-readable numerical summary.
- `figures/` - vector PDF and raster PNG versions of every generated figure.
- `audit/CORPUS_AUDIT.md` - recursive repository audit and nonduplication
  boundary.
- `audit/SOURCE_AUDIT.md` - source/literature roles and proof boundary.
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

## Compile the report

A current TeX Live installation is sufficient. From the archive root, run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_dyadic_chaos_frontiers.tex
```

Equivalently, run `pdflatex` repeatedly until the table of contents and cross
references stabilize. The supplied PDF was built with latexmk 4.86 and pdfTeX
1.40.26 (TeX Live 2025/dev). Standard packages are used, with Libertinus fonts
when available and Latin Modern as a fallback.

## Verification status

- All theorem, equation, figure, and bibliography references resolve.
- The final PDF has 34 A4 pages and embedded fonts.
- The PDF was preflighted and rendered page-by-page at 180 dpi.
- No clipping, overlapping text, broken glyphs, or black rendering artifacts
  were observed.
- The experiment outputs were regenerated from a fresh run before packaging.

## Integrity check

From the archive root:

```bash
sha256sum -c SHA256SUMS
```

## Repository filing status

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
Ten CSV files were then normalized from CRLF to the repository's required LF
line endings; `SHA256SUMS` is the authoritative current-package ledger.

This is a quick archival intake only.  The submitted TeX and PDF have not been
edited or rebuilt, and the numerical program has not been replayed.  In
particular, the report's theorem, novelty, and conjecture labels describe
manuscript status rather than Lean verification.  A hostile claim audit,
claim-by-claim Lean crosswalk, deterministic replay, canonical-preamble
normalization, Type-3 plot-font repair, and exactly-three-pass PDF rebuild are
explicitly deferred until after publication of this intake checkpoint.
