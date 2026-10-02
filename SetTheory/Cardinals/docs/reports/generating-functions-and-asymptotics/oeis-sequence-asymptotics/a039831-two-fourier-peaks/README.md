# Two Fourier Peaks and a Moving Lattice Maximum

**A proof of the OEIS A039831 asymptotic conjecture, four correction orders,
a smoothing hierarchy, and inverse growth**

Research report prepared for Vladimir Reshetnikov, October 1, 2026.

## Main result

Let M_n be the largest coefficient of

    P_n(q) = product_{j=1}^n (1 + q + q^3 + ... + q^(2j-1)).

The article proves

    M_n = 3 (n/e)^n [1 - 431/(300 n)
                    + 23085971/(1764000 n^2) + O(log(n)/n^3)].

It gives explicit relative terms through n^-4 and an arbitrary-algebraic-order
finite formula. A log-periodic lattice loss first appears at order n^-3;
a secondary Fourier contribution contributes a parity-dependent term at
order n^-4. Although smaller, it changes the maximizing exponent infinitely
often. The number of failures of principal-peak rounding through N is
bounded above and below by positive multiples of log N.

The report also proves a fixed-smoothing suppression law, inverse-index
formulas using the principal Lambert W function, and a qualified integer
threshold bracket. Nine further research topics are proposed.

## Proof and priority status

These are ordinary mathematical proofs in the article, not Lean/Rocq-checked
theorems and not independently referee-reviewed results. The supplied
programs check finite identities and computations; they do not verify the
analytic remainders. Numerical error measurements are not interval bounds.

A039831 still labels the leading estimate a conjecture in the OEIS record
inspected on October 1, 2026. A targeted literature/repository audit did not
identify an earlier proof of the particular result. That is not an exhaustive
publication-priority claim. The Fourier/Edgeworth method itself is classical.
The separate distinct-coefficient conjecture in A039824 is NOT resolved here.

## Contents

- `article.tex`, `article.pdf`: editable source and compiled 18-page report.
- `verify.py`: exact sliding convolution, independent small-row convolution,
  exact rational moment and signed-cumulant tests, numerical comparisons,
  and inverse checks. Its main run regenerates `data/`.
- `derive_coefficients.py`: exact symbolic cumulant/Hermite derivation and
  assertions for the four principal-neighborhood correction coefficients
  and the displayed logarithmic coefficients.
- `all_orders.py`: evaluator for the finite arbitrary-order formula in
  Theorem 4.1. It uses exact rational cumulants, then mpmath evaluation.
- `data/numerical_results.csv`: all integer maxima and maximizing exponents
  through n=400, numerical means, normalized maxima, approximation errors,
  and adjacent-coefficient diagnostics.
- `data/inverse_results.csv`: inverse errors at n=50, 100, 200, 400.
- `verification_output.txt`, `symbolic_output.txt`, `all_orders_output.txt`:
  actual outputs of the recorded test runs.
- `SOURCE_MANIFEST.md`: source URLs, inspection scope, and provenance.
- `requirements.txt`: pinned Python dependency versions used for the checks.

No third-party paper, repository source file, or standalone font is bundled.

## Build the PDF

A normal TeX installation with pdfLaTeX and the packages listed in the
preamble is sufficient; no external images or bibliography processor is needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Run a third pass if a first build requests it for the table of contents.
The delivered build has no undefined references, overfull-box warnings,
underfull-box warnings, or package warnings in its final pass.

## Reproduce the calculations

Tested with Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
The code uses Python 3.10+ syntax. Once the dependencies are installed,
all scripts run without network access.

```sh
python -m pip install -r requirements.txt
python verify.py --max-n 400 --digits 70
python derive_coefficients.py
python all_orders.py --n 100 --k 4954 --order 8 --digits 70 --check
```

The first command installs dependencies and normally needs network access.
`verify.py` overwrites its two CSV outputs. To use another destination:

```sh
python verify.py --max-n 100 --out scratch_data
```

`derive_coefficients.py` overwrites `symbolic_output.txt` beside the script.
The archived coefficient rows were computed independently, not downloaded
from the OEIS b-file. The first twenty maxima were checked against the
OEIS entry and every row's mass against the exact integer `(n+1)!`.

The default exact run through 400 took about 16 seconds in the build
environment; time and memory requirements depend on the machine. The count
is O(N^3) integer additions/subtractions through N, not O(N^3) bit operations.
Integers grow with N. No arbitrary-order convergence guarantee is implied by
the parameter `--order`: increasing asymptotic order at fixed n need not help.

## Interpretation of the data

Each `relerr_*` field is `(approximation - true maximum) / true maximum`.
For orders 3 and 4, the approximation is evaluated at the exactly computed
maximizing exponent. Order 4 includes the parity correction.
The `mode_prediction` column uses only the first-order parity threshold;
it is not claimed exact for all n. In particular, its prediction at n=56
is wrong, as disclosed in the article and recorded output.
`adjacent_scaled_remainder` is n^5 times the error of equation (6.4) for
the adjacent candidates, normalized by 3(n/e)^n.

At n=400 the four-power truncation has relative error about 8.01648e-10.
At n=100, k=4954, the separate exact-cumulant finite formula at weight
budget R=8 has relative error about 1.14574e-10. It retains higher terms
implicitly through its exact cumulants and variance, so it is not the same
approximation as the four-power truncation.

The inverse formula is proved at matched inputs y=M_n. For arbitrary y the
integer threshold requires rounding with the explicit boundary-layer caveat;
a smooth inverse alone cannot uniformly approximate the staircase to o(1).
