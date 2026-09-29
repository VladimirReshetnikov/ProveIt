# Finite-Prefix Corrections and Dual Certificates for Polyomino Growth

Research report prepared for Vladimir Reshetnikov, September 2026.

## Main results

The article proves a finite-prefix correction theorem for proper positive
polynomial recurrences. Applied to Bui's seventeen-neighborhood system, the
supplied enumeration and rational certificate give

    lambda <= 2249/500 = 4.498 < 4.5.

Here lambda is the growth constant of fixed square-lattice polyominoes:
translation is identified, but rotations and reflections are not identified.
The more precise coefficient bound is

    A_n <= (927884613/10^9) (2249/500)^n,  n >= 1.

A second theorem gives balanced integer-monomial certificates for divergence,
with a completeness theorem for productive, strongly connected, nonlinear
positive polynomial systems. The supplied 53-weight certificate and the
repository's earlier upper certificate establish

    4.52349 <= mu_original <= 4.5235.

**mu_original is the growth of the original equality recurrence. Its lower
bound is NOT a lower bound on actual polyomino growth.**

The article also proves a spectral stability/obstruction theorem for the
prefix hierarchy, gives a scalar example where exact prefixes never close
the asymptotic gap, and proposes ten specific further research directions.

## Status and trust boundary

This is an AI-assisted research draft with full mathematical proofs and
reproducible computations, not an independently refereed paper. No new Lean
formalization is claimed. The imported geometric recurrence lemma is Bui's
Lemma 4 and the corresponding existing ProveIt development. The existing
Lean source was inspected but was not rebuilt in this work.

The new numerical bound depends on the exact marked-occurrence table through
size 18. Its enumerator's mathematical correctness argument is in the article.
The arithmetic checker verifies the certificates and consistency of the table;
it does not, by itself, prove that the table enumerates the stated objects.
Regeneration of the enumeration is a separate check.

Classical geometric-programming ideas, weighted AM-GM, and Redelmeier-style
enumeration are prior tools. The new bound and applications are contributions
of this report relative to the inspected repository snapshot and sources;
there is no claim of an exhaustive priority search.

## Source snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9
Project: Combinatorics/Polyominoes/KlarnerConstant/

The inspected files include README.md, Support/verify_certificate.py,
Lean/KlarnerConstant/Patterns.lean, and
Lean/KlarnerConstant/GeometricComplete.lean.

Published source: Vuong Bui, *A convolutional approach to bounding the number
of polyominoes*, arXiv:2511.00461v2, 6 May 2026.
https://arxiv.org/abs/2511.00461v2

The complete bibliography and dependency audit are in article.pdf.
No repository files were changed by preparing this archive.

## Read and build

- `article.pdf`: complete report.
- `article.tex`: main source; uses generated tables in `tex/`.
- `data/`: exact data, certificates, verification transcript, exploratory estimates.
- `code/`: verifiers, enumerators, and optional numerical discovery programs.

Build the PDF with a TeX Live installation containing newpx, amsmath,
mathtools, geometry, microtype, booktabs, longtable, enumitem, fancyhdr,
titlesec, listings, tcolorbox, hyperref, and cleveref:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

## Exact certificate replay

Python 3.10 or later; **no third-party Python packages required**:

```sh
python3 code/verify.py --report data/verification.json
python3 code/check_profile.py data/profiles_18.csv
```

The verifier uses arbitrary-precision integers and `fractions.Fraction`.
It checks properness, productivity, strong connectivity, nonlinearity,
nonnegative defects, five occupancy partitions, twelve upper certificates,
the 53 monomial balance equations, an exact logarithmic enclosure, and the
old 4.5235 supersolution. All decisions are made without floating point.
The archived successful output is `data/verification.txt`.

To refresh the tables after a successful replay:

```sh
python3 code/make_tables.py
```

## Recompute the enumeration

A C++17 compiler with GCC/Clang-compatible `__builtin_ctz` is needed for the
incremental enumerator. The direct-scanning implementation does not use that
intrinsic. Both programs reject sizes outside 1..18; the article's storage
and overflow bounds apply to that range.

```sh
c++ -O3 -std=c++17 code/enumerate.cpp -o enumerate
./enumerate 18 > regenerated.csv
python3 code/check_profile.py regenerated.csv
```

This enumerates 1,540,820,542 size-18 objects, and 2,083,404,030 objects in
all sizes through 18. It is much slower than certificate replay. A smaller
prefix is useful for a smoke test:

```sh
./enumerate 11 > prefix11.csv
python3 code/check_profile.py prefix11.csv
c++ -O3 -std=c++17 code/enumerate_direct.cpp -o enumerate_direct
./enumerate_direct 11 > direct11.csv
python3 code/check_profile.py direct11.csv
```

The direct-scanning and incremental implementations agreed through size 16
in this research run. An independent Python set-expansion implementation
agreed through size 11; its recorded output is `data/profiles_python_11.json`.
The two C++ versions share the same include/exclude generation strategy, so
their agreement is stronger evidence about pattern counting than an entirely
independent enumeration of all size-18 objects would be. The size-18 unmarked
counts were also compared with OEIS A001168, but no external database is an
input to the proof or the checker.

## Optional exploration (not part of proof verification)

Install NumPy, SciPy, and SymPy, for example:

```sh
python3 -m pip install -r requirements-discovery.txt
```

`code/research.py` contains a separate coordinate-set pattern encoding,
set-based reference enumeration, and floating-point critical-point search.
To regenerate the independent Python prefix (memory grows rapidly):

```sh
python3 code/research.py enumerate 11 reference11.json
```

Without arguments it writes new numerical critical estimates to
`critical_estimates_new.json` in the working directory, leaving the archived
estimates unchanged. Small numerical residuals do not certify singularities,
optimality, or growth constants.

`code/discover_certificates.py` shows the numerical discovery and rational
rounding used in this work. It is an exploratory research script and may
write certificate files under `data/`; run it on a copy of this archive.
Only subsequent exact certificate replay establishes their inequalities.

## File integrity

`SHA256SUMS` records hashes of the delivered files other than the checksum
file itself. On platforms with `sha256sum`, run:

```sh
sha256sum --check SHA256SUMS
```
