# Binary Runs in Rueppel Hankel Determinants

**Four conjectures, a polynomial refinement, and a correction**  
Research manuscript prepared for Vladimir Reshetnikov, 19 September 2026.

## Start here

Read `rueppel_hankel.pdf`. Its complete LaTeX source is
`rueppel_hankel.tex`, with the first-values table in `tables.tex`.
The paper gives detailed, self-contained proofs, not just computational evidence.

Let `r(x) = sum_{j>=0} x^(2^j - 1)`, and let `H_n(f)` be the determinant
of the **n by n** matrix of coefficients `f_(i+j)`, with `H_0 = 1`.
Let `R(n)` count runs of equal bits in the binary expansion of a positive
integer n, without leading zeros. Put `g = n xor (n >> 1)` and `eps = g & 1`.
The main result, for every n >= 1, is the polynomial identity

    H_n(t*x + 1/r(x^2))
      = (-1)^(1 + eps + floor(R(n)/2)) * (eps + (R(n)-eps)*t^2).

In particular, the absolute value at t=1 is R(n). The proof uses parity
blocks, complementary minors for reciprocal series, and four elementary
Rueppel determinant sequences.

## Conclusions

The manuscript supplies proofs of the statements numbered **8, 10, 13,
and 23** in Paul Barry's *2021* paper, not the identically numbered
statements in his earlier paper. The main polynomial identity strengthens
Conjecture 13. Further consequences include all exceptional complex
parameter values, exact signed distributions, and dyadic sums.

Conjecture 22 **as printed** fails at its index j=2 (matrix order 3):
the proposed squared equality would be `1 = -1`. The paper proves a valid
signed replacement and, more generally, a complement--difference square
identity for arbitrary moment sequences. It does not claim to have
identified the author's intended correction.

**Status and priority:** This is an unrefereed research manuscript. The
original source still labels the selected statements conjectures, and a
focused search did not identify a later resolution. This is not proof of
bibliographic priority. Foundational Rueppel determinant identities and
related binary-run results are explicitly credited to earlier work. The
article has not been formally verified in Lean or another proof assistant.

## Reproduce the computations

Use Python 3.10 or newer. No external Python packages are required.
Run these commands from this directory:

    python -m unittest discover -s tests -v
    python code/verify.py

The verification script writes CSV and JSON data under `data/` by default.
It overwrites files of the same names, so choose a new output directory
when retaining the original run is important:

    python code/verify.py --out new_audit

The saved audit passed 1,192 exact Rueppel-related determinant evaluations,
including consecutive orders 0 through 64 and selected orders 65, 127,
and 128. It also checked the general moment identity on 500 instances,
the shifted-sign recurrence through index 65,535 and at 1,000 random
256-bit indices, and dyadic distributions/sums. Random seeds are fixed.

The unit tests independently compare the Bareiss determinant engine with
Leibniz permutation expansion on 140 random matrices and check reciprocal
minor identities, digit identities, edge cases, and parameter families.
The matrix determinant engine does not call the conjectured/derived
binary formulas. All arithmetic in these audits is exact integer arithmetic.

Finite checks are error-detection measures. The all-index claims depend
on the mathematical proofs in the article, not on those checks.

Optional larger finite audit (not the recorded run):

    python code/verify.py --max-size 96 --large-size 192 --digital-bits 18 --out larger_audit

## Use the formulas

From the project root:

    import sys
    sys.path.insert(0, "code")
    from rueppel import parameter_coefficients, parameter_hankel

    print(parameter_coefficients(10))       # (1, 3), meaning 1 + 3*t^2
    print(parameter_hankel(10, t=1))        # 4
    print(parameter_coefficients(10**100))  # (0, 122), meaning 122*t^2

The code's determinant index is always a matrix size. Barry's sequence
index j corresponds to matrix size n=j+1. The size-zero value is separate.

## Build the PDF

A current TeX Live or MiKTeX distribution is sufficient. Required packages
include `newpxtext`, `newpxmath`, `sourcesanspro`, `amsmath`, `amsthm`,
`mathtools`, `geometry`, `microtype`, `booktabs`, `enumitem`, `listings`,
`fancyhdr`, `titlesec`, `float`, `tcolorbox`, `hyperref`, and `cleveref`.
The fonts are provided by those TeX packages; no font files are distributed
in this archive. There is no external bibliography database or shell-escape
requirement.

    pdflatex -interaction=nonstopmode -halt-on-error rueppel_hankel.tex
    pdflatex -interaction=nonstopmode -halt-on-error rueppel_hankel.tex
    pdflatex -interaction=nonstopmode -halt-on-error rueppel_hankel.tex

Alternatively, `make pdf` uses those commands. `make test` runs the unit
tests. `make verify` reruns the main audit, and `make table` regenerates the
first-values table. `make clean` removes TeX build intermediates only.

## Contents

- `rueppel_hankel.tex`, `tables.tex`, `rueppel_hankel.pdf`: article.
- `code/rueppel.py`: formulas, formal reciprocals, and exact determinants.
- `code/verify.py`: reproducible finite audits and data generation.
- `code/make_table.py`: regenerates `tables.tex`.
- `tests/test_rueppel.py`: independent unit tests.
- `data/`: CSV tables, JSON summaries, and captured run/test logs.
- `SOURCE_AUDIT.md`: exact problem source, page locations, and scope caveats.
- `Makefile`: PDF and computation targets.

## Primary sources

Paul Barry, *Conjectures and results on some generalized Rueppel sequences*,
arXiv:2107.00442v2 (4 July 2021):
https://arxiv.org/abs/2107.00442

Jean-Paul Allouche, Guo-Niu Han, and Jeffrey Shallit, *On some conjectures of
P. Barry*, Journal of Number Theory 228 (2021), 108-132;
arXiv:2006.08909v2:
https://arxiv.org/abs/2006.08909

OEIS: https://oeis.org/A036987 , https://oeis.org/A005811 ,
https://oeis.org/A268411 , https://oeis.org/A339422 .

Other authors' papers and font files are not included.
