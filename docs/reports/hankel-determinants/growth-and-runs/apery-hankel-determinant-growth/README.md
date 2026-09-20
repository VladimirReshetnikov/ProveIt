# Apéry Hankel growth: a proof and reproducible computations

**Main result.** For

\[
A_k=\sum_{j=0}^k\binom{k}{j}^2\binom{k+j}{j}^2,
\qquad D_n=\det(A_{i+j})_{0\le i,j\le n},
\]

this report proves

\[
\log D_n=n(n+1)\log\!\left(\frac{17+12\sqrt2}{4}\right)+O(n).
\]

In particular, it proves the limit conjectured in the September 13, 2026
revision of OEIS A228143. The proof uses Edgar's known moment-density theorem;
it does not reprove that theorem. All subsequent determinant arguments are
included in the article. The accessed OEIS entry still labelled the precise
limit as a conjecture. This is not a claim of worldwide priority.

The report also proves an explicit law for
`det(A_(m*(i+j)+r_n))` with fixed positive integer m and r_n/n -> rho >= 0,
and proves that the formal ordinary generating series of D_n is not D-finite.
It does not claim a full multiplicative asymptotic equivalent or a limit of
D_n/(D_(n-1)*(C/4)^(2n)). It is an AI-authored research note, not a peer-reviewed
or proof-assistant-certified publication.

## Main files

- `apery_hankel_growth.pdf` and `apery_hankel_growth.tex`: 12-page report.
- `data/determinants_0_200.txt`: **not distributed** (2.4 MB). Exact D_0
  through D_200, D_200 having 37,308 digits; rebuild with
  `build/apery_gmp 200 > data/determinants_0_200.txt`.
- `code/apery_exact.py` and `code/apery_gmp.cpp`: two exact implementations.
- `code/verify.py` and `data/verification.json`: independent exact checks.
- `data/shift_experiments.json`: exact samples of the shifted/dilated families.
- `sources.md`, `review_checklist.md`, `oeis_submission_draft.txt`: source audit,
  mathematical review points, and an unsubmitted editorial suggestion.

The `data/*_table.tex` files and `figures/convergence.pdf` are included because
the main LaTeX source inputs them. All needed source assets are in this ZIP.
No binaries, font files, downloaded third-party papers, or checksum files are
included.

## Rerun the checks (standard-library Python only)

Python 3.10 or later is sufficient. The recorded run used Python 3.13.5.
From this directory:

```sh
python3 code/verify.py
```

The verifier checks 401 moments against their defining binomial sums, the
10-term displayed OEIS prefix, 41 Python/GMP determinants, 13 independent
rational-Gaussian determinants, 33 modular-Gaussian determinants, 64 shifted
condensation identities, 32 rational power-weight determinants, and 501
central-binomial inequalities. A failed check raises an error. These are finite
arithmetic tests, not the proof of the limit.

## Regenerate exact determinants

Small and medium cases require only Python:

```sh
python3 code/apery_exact.py --n 40 --output data/recomputed.txt
python3 code/apery_exact.py --n 20 --stride 2 --shift 5 --output data/example.txt
```

For the complete 200-index run, use C++17 with GMP development libraries:

```sh
mkdir -p build
g++ -O3 -std=c++17 code/apery_gmp.cpp -lgmpxx -lgmp -o build/apery_gmp
build/apery_gmp 200 > data/determinants_0_200.txt 2> data/gmp_run.log
python3 code/verify.py
```

The program writes `index exact_integer` records. The determinant indexed n
has matrix order n+1. Its optional arguments are stride (default 1) and shift
(default 0). Every integer division is checked; a nonexact division or a
nonpositive leading pivot causes failure. The delivered run checked 1,353,400
symmetric Bareiss divisions and took about 124 seconds for the determinant
phase in this runtime; that timing is not a guarantee on other machines.

The elimination uses O(n^3) integer arithmetic operations and O(n^2) integer
storage locations. These are not bit-complexity bounds.

## Reproduce the shifted experiments

```sh
python3 code/shift_experiments.py --gmp build/apery_gmp --indices 10,20,40,80
```

Without `--gmp`, the script uses Python and defaults to indices 10 and 20.
It checks the cases `(m,r_n)=(1,n),(2,0),(2,n)`. The shift is fixed across
each matrix, not changed with the row or column. Samples with n <= 20 are
cross-checked with the Python implementation even when GMP generates them.

## Tables and plot

The existing tables and figure are sufficient to compile the report. To
regenerate them, install the optional plotting dependencies and run:

```sh
python3 -m pip install -r requirements-plots.txt
python3 code/make_figures.py
```

This uses logarithms of exact integer determinants, never a floating-point
determinant. The delivered run compared evaluations at 90 and 180 decimal
digits; their maximum absolute difference across the main diagnostics was
less than 8e-87. This is a precision-stability check, not interval certification.
The figure uses only the proved limit as a reference line.

## Compile the article

A TeX Live installation with pdfLaTeX, Libertinus Type 1 text and math fonts,
AMS packages, tcolorbox, graphics, and hyperref is sufficient:

```sh
pdflatex -interaction=nonstopmode -halt-on-error apery_hankel_growth.tex
pdflatex -interaction=nonstopmode -halt-on-error apery_hankel_growth.tex
```

Alternatively, `make pdf` compiles into `build/` and copies out the final PDF.
No font files are distributed. The delivered PDF was rendered and visually
inspected. The source has no unresolved citations or overfull boxes.

## Source and novelty scope

The critical source is G. A. Edgar, *The Apéry Numbers as a Stieltjes Moment
Sequence*, arXiv:2005.10733v2 (2020). The argument exploits the positive density
on the full interval [0,17+12*sqrt(2)], including the small part to the left of
the interior singularity. Classical orthogonal-polynomial and Cauchy-determinant
methods are proved where needed. The report's contribution is their explicit
application to the selected conjecture and its shifted extensions, not the
invention of those general methods.

The source audit is dated September 18, 2026. The draft OEIS comment has not
been submitted, and no external repository or OEIS entry has been modified.
