# Bell-scale growth of OEIS A088714

> **`data/coefficients.txt` is not distributed** (1.3 MB). Rebuild it with `python code/coefficients.py --output data/coefficients.txt`.
This archive accompanies the article **Bell-Scale Growth of OEIS A088714**
(September 20, 2026). It contains a self-contained proof, exact coefficient data,
and reproducible implementation checks.

## Proved result

For A(x) = sum a_n x^n, defined formally by

    A(x) = 1 + x A(x)^2 A(x A(x)),    a_0 = 1,

the article proves

    log(a_n) = n log(n) - n log(log(n)) - n
               + O(n log(log(n))/log(n)),

and consequently

    a_n^(1/n) ~ n/(e log(n)).

This is an nth-root/logarithmic asymptotic, NOT the assertion
`a_n ~ (n/(e log(n)))^n`. The article proves explicit finite-index upper and
lower bounds as well. The ordinary generating function has radius zero;
the exponential generating function is entire.

The finer formula

    a_n ~ C Bell_n exp(W(n)^2 + 3 W(n))

is separately labeled a CONJECTURE. Neither its constant nor the existence
of its limit is asserted to have been proved. The article identifies a
specific ratio estimate sufficient to prove it.

## Contents

- `article.tex` and `article.pdf`: the complete article and compiled PDF.
- `code/coefficients.py`, `code/compute_gmp.cpp`: exact triangular-recurrence
  implementations in Python and C++/GMP.
- `code/verify.py`: independent polynomial checks, positivity checks,
  comparison-bound checks, and Python/GMP coefficient agreement.
- `code/analyze.py`: high-precision diagnostics and the article's numerical table.
- `data/coefficients.txt`: exact pairs `n a_n` for n = 0..1200, generated here,
  not downloaded from an OEIS b-file.
- `data/diagnostics.csv`: numerical diagnostics for n = 2..1200, with 40
  significant digits in the stored floating-point quantities.
- `data/diagnostics_table.tex`: the table included by `article.tex`.
- `data/verification.txt` and `data/analysis_output.txt`: actual execution output.

## Reproduce the checks

Run commands from this directory. Python 3.10 or later is suitable for the
provided type-annotated scripts. The exact coefficient and verification code
uses only the Python standard library.

    python3 code/verify.py

The supplied run verified the first 21 OEIS terms, independently recomputed
coefficients through n=400 in Python, checked the defining functional equation
and inverse identities through degree 40, checked the difference-polynomial
identity and positivity through n=80, and checked the finite bounds through
n=150 at the five reported integer Poisson means. All checks passed.

These finite checks audit the implementation. The all-index theorem is proved
in the article; it is not inferred from the finite checks.

## Recompute coefficients

The reference implementation is deliberately simple:

    python3 code/coefficients.py --n 400 --output coefficients_python.txt

For the full supplied range, an optional C++17 compiler and the GMP development
library give a faster implementation:

    g++ -O3 -std=c++17 code/compute_gmp.cpp -lgmpxx -lgmp -o compute_gmp
    ./compute_gmp 1200 data/coefficients.txt

Both implementations use N(N+1)(N+2)/6 big-integer products and O(N^2)
integer cells. Those are arithmetic counts, not constant-cost bit counts.
The C++ executable is not included in the archive.

## Recompute diagnostics and build the article

The optional diagnostic script requires `mpmath`; `requirements.txt` lists it.

    python3 -m pip install -r requirements.txt
    python3 code/analyze.py --precision 70
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The supplied numerical table uses the exact integers as input. Decimal
arithmetic is used only to evaluate logarithms, roots, Lambert W, and ratios.
The numerical constant estimator is exploratory, not a certified enclosure.

A `Makefile` is included for building, checking, and regenerating diagnostics.
No network access is needed to use the supplied data or run the exact checks.
The bibliography identifies the OEIS definition and the NIST DLMF Bell-number
and Lambert-W comparison formulas consulted for the article.
