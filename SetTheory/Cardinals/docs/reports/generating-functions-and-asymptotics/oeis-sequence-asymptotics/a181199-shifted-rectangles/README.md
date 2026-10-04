# Fixed-height shifted rectangles

## An unconditional proof of the A181199 asymptotic, all-order expansions, and an algebraicity dichotomy

Prepared for Vladimir Reshetnikov — October 3, 2026.

**Status:** AI-assisted, unrefereed research manuscript. The article contains proofs, but they have not been independently peer reviewed or checked in a proof assistant. Historical priority is not certified. No submission to OEIS or change to the ProveIt repository has been made.

## Main mathematical content

Let T_m(n) count m-by-n arrays of the integers 1,...,mn increasing in rows, columns, diagonals, and downward antidiagonals. The number of rows m is fixed while the row length n grows.

The article proves

    T_m(n) ~ K_m * m^(m*n) * n^(-(m^2-1)/2),
    K_m = sqrt(m) * product(j!, j=0,...,m-1)
          / (2^(m*(m-1)) * (2*pi)^((m-1)/2)).

It gives an effective all-order inverse-power expansion, proves the first two correction coefficients symbolically at every height, and evaluates five corrections for heights two through six. At m=5 this proves the asymptotic labeled conjectural in OEIS A181199 when inspected on October 3, 2026. The argument does not assume any conjectured sequence recurrence.

Further results include the algebraicity classification of the ordinary generating function (algebraic exactly at heights one and two), a limiting ratio to ordinary rectangular tableaux, Gaussian Vandermonde and trace-zero intermediate-shape laws, eventual strict log-convexity, and inverse-index asymptotics. Seven further research questions and proposed approaches are included.

The key exact identity replaces the count by a binomial expectation of a rational squared-Vandermonde weight, with a nonnegative boundary error at most 2*m*2^(-n) in probability normalization. A self-contained shifted-hook proof is included in Appendix A.

## Contents

- `article.pdf` — compiled research article.
- `article.tex` — complete LaTeX source, including bibliography; no external bibliography or image files required.
- `build.sh` — three-pass PDF build, runnable from any working directory.
- `code/coefficients.py` — exact rational coefficient generator; no sequence data or guessed recurrence used.
- `code/tableaux.py` — independent row-state and cell-poset enumerators, shifted hook product, exact interior lower bound.
- `code/verify.py` — finite exact verification suites.
- `code/numerics.py` — high-precision numerical diagnostics, not interval certificates.
- `data/` — coefficient tables, selected OEIS reference integers, independently regenerated counts, and verification/numerical records.
- `notes/SOURCES_AND_STATUS.md` — source audit and distinctions between established background, proved statements, and unresolved questions.
- `notes/PROPOSED_OEIS_ADDITIONS.txt` — draft mathematical additions, not submitted.
- `requirements-numerics.txt` — optional dependency for the numerical diagnostics.
- `SHA256SUMS.txt` — checksums for the distributed files other than this checksum list itself.

## Reproduce

Use Python 3.10 or later. From this directory:

```sh
python3 code/verify.py
python3 code/coefficients.py --height 5 --order 5
python3 code/coefficients.py --height 5 --order 5 --output data/coefficients_m5.json
```

These commands use only the Python standard library. Do not run the verifier with `python -O`, which disables assertions.

Optional numerical diagnostics:

```sh
python3 -m pip install -r requirements-numerics.txt
python3 code/numerics.py
```

The numerical script uses 90 decimal digits. Its reported errors are diagnostic decimal approximations, not certified intervals.

Build the article with a conventional TeX Live installation containing the packages named in the preamble:

```sh
bash build.sh
```

On Windows, the three `pdflatex` commands in that script can instead be run in a terminal from this directory. The New TX fonts are normal TeX dependencies; no font files are redistributed.

## Verification and provenance

The recorded run passes 471 checks: independent small-poset comparisons, shifted-hook prefix checks, exact threshold identities and boundary inequalities, Catalan controls, selected OEIS values, universal correction formulas, and moment identities. For each of A181198 and A181199, the values at n=1,...,10,20,40 were independently regenerated and matched to the OEIS reference data.

The values at n=80 are **reference inputs only** and were not independently regenerated in this run. The data file records the original entry and b-file URLs. The full third-party articles and full b-files are not included.

These tests corroborate the mathematics but do not replace the proofs. The script runtime in the verification record is machine-dependent.

## Limits of the claims

The specific conjectured recurrences for A181198 and A181199 are not proved here. The all-order expansion is for fixed m and a fixed truncation order; it is not a growing-height theorem or a complete exponentially improved transseries. The probabilistic results concern one-time distributions, not process convergence. Inverse-index approximations are not exact integer-threshold certificates. The leading asymptotic already recorded for height three is recovered, not claimed as new.

The inspected ProveIt revision is `6bf7f30d0352f7596e70928b3d4f304914075907`. Identifier searches for A181198 and A181199 returned no report. That limited search and the literature audit do not establish global historical priority.
