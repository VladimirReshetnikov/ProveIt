MATRIX COMPOSITIONS: EXACT SPECTRA, HANKEL PRODUCTS, AND UNIFORM ASYMPTOTICS
OEIS A261781 and A261784

Research prepared for Vladimir Reshetnikov, October 3, 2026 (Pacific time).

CONTENTS

matrix_compositions.tex
    Complete LaTeX article source, using the figure provided below.
matrix_compositions.pdf
    Compiled article.
README.txt
    This file.
SOURCE_AUDIT.txt
    Scope of the repository and primary-literature audit, with URLs and
    a distinction between established formulas and the present extensions.

code/verify.py
    Exact enumeration, recurrence and determinant checks, plus high-precision
    coupon-window and dense-diagonal diagnostics. Includes the finite
    Gaussian-moment evaluation of both diagonal correction coefficients.
code/make_figures.py
    Regenerates the static scientific coupon-window figure and its curve data.
code/requirements.txt
    Pinned Python dependency versions used for the supplied run.

figures/coupon_window.pdf
    Vector figure used by the article.
figures/coupon_window.png
    The same figure as a 220-dpi PNG preview.

data/oeis_rows.json
    The nine supplied rows of A261781 matched by the exact calculations.
data/recurrence_checks.json
    Exact numerator and denominator coefficients, gcd checks, recurrence
    indexing, and initial impulses for fixed heights k=1,...,10.
data/hankel_determinants.csv
    Full-rank tail Hankel determinants for k=1,...,5 and shifts 1,2,3.
data/initial_hankel_determinants.csv
    Initial Hankel determinants of size k(k+1)/2+1 for k=1,...,4.
data/weighted_hankel_checks.json
    Five symbolic determinant identities in the column weight u.
data/pole_bound_checks.csv
    Thirty comparisons of exact coefficients with the uniform pole estimate.
data/coupon_window.csv
    Fifteen coverage-window cases with target s=-1,0,1 and
    k=20,50,100,500,1000. Includes the actual integer n, the actual window
    coordinate, moving Poisson mean eta, probability estimates, analytic
    Bonferroni/pole error budgets, and first-correction diagnostics.
data/coupon_curve.csv
    The 393 finite-k points used in the figure.
data/diagonal_constants.json
    High-precision evaluations of the saddle, leading constants, beta1,
    and beta2 for the A261784 diagonal T(2N,N).
data/diagonal_asymptotics.csv
    Exact integer diagonal terms and asymptotic diagnostics for
    N=5,10,20,30,50,75,100.
data/verification_summary.json
    Exact-check and numerical-run receipt with dependency versions.
data/figure_generation_summary.json
    Figure-generation receipt, dimensions, precision, and point count.

NOTATION

n is the total matrix mass; k is the number of ordered rows (height).
A(n,k) counts matrices with nonzero columns, allowing zero rows.
T(n,k) also requires every row to be nonzero. The variable u marks columns.
The coverage probability is T(n,k)/A(n,k). All logarithms are natural.

PYTHON DEPENDENCIES

Python 3.10 or later is required. The supplied computations used:

    Python       3.12.14
    mpmath        1.3.0
    SymPy        1.14.0
    matplotlib   3.10.8

From this package's root directory, install the pinned dependencies with:

    python3 -m pip install -r code/requirements.txt

Then regenerate the checks, data, and figures:

    python3 code/verify.py
    python3 code/make_figures.py

Both programs run locally and use no network access. They overwrite their
generated data/figure files. The supplied run took approximately 0.3 seconds
for verification and 2.3 seconds for figure generation; timings depend on
the machine. The default arithmetic precision for numerical diagnostics is
120 decimal digits.

LATEX BUILD

A TeX distribution with pdflatex and latexmk is required. The article uses
standard packages: lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, enumitem, graphicx, xcolor, hyperref,
and fancyhdr (plus the standard fontenc package).

From this package's root directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error matrix_compositions.tex

The supplied PDF figure is already present, so Python is not needed merely
to compile the article. If latexmk is unavailable, run pdflatex repeatedly
until cross-reference warnings have disappeared:

    pdflatex -interaction=nonstopmode -halt-on-error matrix_compositions.tex
    pdflatex -interaction=nonstopmode -halt-on-error matrix_compositions.tex

Optional removal of auxiliary LaTeX build files, retaining the PDF:

    latexmk -c matrix_compositions.tex

VERIFICATION SCOPE

The exact calculations use arbitrary-precision integers and symbolic
polynomials. The independent construction routes agree on all 341 tested
(n,k) pairs for each of A and T, and the supplied OEIS rows match exactly.
The recurrence, determinant, and initial-impulse checks cover the finite
ranges specified in data/verification_summary.json.

Coupon probabilities are evaluated using Bonferroni bounds with an explicit
allowance for the uniform dominant-pole replacement error. Five coupon
cases are also compared with independent exact integer ratios. The analytic
truncation and pole-replacement bounds are separate from decimal evaluation:
the endpoints use high-precision floating arithmetic and are NOT formally
certified by directed rounding.

The numerical comparisons illustrate the proofs and help detect arithmetic
or implementation errors. They are not mathematical proofs. The article
contains the proofs and states their assumptions. The derived second
diagonal coefficient is evaluated from the finite Gaussian-moment rule;
it is not fitted from the integer data. No proof-assistant verification or
historical-priority guarantee is claimed.
