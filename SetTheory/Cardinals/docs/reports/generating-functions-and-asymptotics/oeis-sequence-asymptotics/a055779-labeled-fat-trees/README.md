# Report203

## Uniform asymptotics and inverses for labeled fat trees

This package supplies the complete article, editable TeX, compiled PDF, and
reproducible code for the weighted fat-tree sequence A055779 and its relation
to A295623. The main expansion holds to every **fixed** order uniformly over
real M >= 1. The Lambert-centered inverse fixes M. A separate elementary
appendix proves finite-n Poisson-deficit bounds and all fixed correction
orders for bounded lambda = n/M.

The exact multiplicity formula is Zaslavsky's prior work. The leading prefactor
is closely implicit in the later A162695 formula, and standard saddle/assembly
methods have substantial prior. No first-prefactor, new general method,
convergent-series, effective-onset, maximal-Poisson-range, or exhaustive-novelty
claim is made. Source details and qualifications are in the article.

## Contents

- `Report203.pdf`: complete 19-page article
- `Report203.tex`: self-contained editable LaTeX source
- `code/`: exact arithmetic, symbolic coefficient/inverse checks, separate
  high-precision diagnostics, and expected recomputed data
- `build.py`: strict whole-package validation, replay, PDF build, and fixed ZIP
- `test_guards.py`: explicit malformed-input, tampering, and article-to-data checks
- `manifests/`: source and whole-package SHA-256 and byte-count manifests

No third-party papers, source-page images, private notes, external notebooks,
or private path dependencies are redistributed. The bibliography links to
primary public sources. No network access is used by the reproduction scripts.

## Requirements

The recorded reference toolchain is:

- CPython 3.12.14
- SymPy 1.14.0 and mpmath 1.3.0, pinned in `requirements.txt`
- `pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian)`
- Installed `pdflatex`, `pdftex`, `kpsewhich`, and the LaTeX packages named in
  `Report203.tex`, including Latin Modern, microtype, AMS, geometry, hyperref,
  enumitem, fancyhdr, xcolor and booktabs

The standard-library exact checks run without SymPy or mpmath:

```sh
python -B code/check.py --exact
```

Install the two pinned Python dependencies into your chosen environment before
running all checks. The package never installs software itself:

```sh
python -m pip install -r requirements.txt
python -B code/check.py --all
```

All checks use explicit exceptions and remain active with `python -O`. The
code runner executes the programs in normal and optimized modes, compares every
output byte with its expected fixture, and rejects optimization-sensitive
assert statements in the selected computational source. See `code/README.md`
for exact finite sample counts and implementation provenance. The package tests also
compare the article's small-n polynomials, first six values, and every numerical
table cell against the replayed exact and diagnostic data. Numerical output
is diagnostic, not interval-certified and not a premise of any theorem.

## Whole-package deterministic replay

Extract the actual release ZIP into a fresh location and enter its `Report203`
directory. Place build outputs outside that directory and use paths that do
not already exist:

```sh
python -B build.py --validate-only
python -B build.py --output ../rebuild-normal --archive ../normal.zip
python -B -O build.py --output ../rebuild-optimized --archive ../optimized.zip
cmp ../normal.zip ../optimized.zip
```

Also compare each rebuilt ZIP with the original distributed ZIP. With the
recorded dependencies and TeX toolchain, every public member and the entire
ZIP must be byte-identical. The builder validates the complete fixed member
allowlist before work, replays all exact/symbolic/diagnostic outputs, compiles
TeX in a fresh temporary environment, verifies both manifests, and compares
all rebuilt members to the extracted package. It reports the rebuilt PDF and
ZIP SHA-256 hashes on stdout. Maintained sources and fixtures are not changed.

The TeX build disables shell escape and uses a fixed `SOURCE_DATE_EPOCH`;
creation dates, trailer IDs and path-bearing pdfTeX metadata are suppressed.
The ZIP has fixed timestamps, permissions, member order and no compression,
avoiding compression-library variation. Fixed manifests explicitly omit the
package manifest's own hash to avoid a circular self-hash; the whole ZIP hash
is reported externally by the build. The source manifest records the PDF
engine banner. Hashes detect changes relative to this package; they are not a
signature or external proof of authorship.

Byte-identical PDF output across arbitrary TeX distributions or package versions
is not promised. Exact and symbolic formulas are portable within the stated
Python dependencies; reproducing the release PDF bytes requires the recorded
TeX toolchain. A mismatched engine is rejected explicitly rather than silently
certified.

For intentional source edits, maintainers may use `--initialize` with fresh
output/archive paths to regenerate manifests. That is a new release build,
not validation of the original. Review all changed claims, data and rendered
pages before distribution.

## Mathematical and source scope

The report proves fixed-order uniform forward asymptotics and a fixed-M
integer inverse directly, without assuming linear interpolation or a universal
single-ceiling rule. The appendix concerns block deficit D = n-K, not edges or
nonsingleton blocks. Its O(1/n) total-variation bound is to the moving Poisson
parameter; a rate to a limiting parameter needs a separate convergence rate.
Finite tests and diagnostics cannot establish any asymptotic or priority claim.
