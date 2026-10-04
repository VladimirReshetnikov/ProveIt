# Exact Inversion of the Partition Function
## A proof of OEIS A306631 and sharp rounding bounds

Research report dated 3 October 2026, prepared for Vladimir Reshetnikov.

## Main deliverables

- `article.pdf`: the compiled research article.
- `article.tex`: the complete, self-contained LaTeX source, including references.
- `code/certify.py`: exact rational-interval verification of the finite part of the proof. Standard library only.
- `results/certificate.json`: successful certificate summary and certified constant enclosures.
- `results/finite_comparisons.csv`: all 1,204 asserted H comparisons, including exact rational enclosure endpoints.
- `code/series.py` and `results/coefficients.json`: twelve exact rational coefficients for each of two inverse constructions, with substitution checks through degree 13.
- `code/experiments.py` and `results/numerics.json`: high-precision illustrations, explicitly not proof certificates.
- `OEIS_update_draft.txt`: proposed mathematical update for independent review, not submitted to OEIS.
- `PROVENANCE.md`: source audit, repository snapshot and scope of the claims.

## What the article proves

For p(n), the ordinary partition number, let F be the increasing inverse of
H(x) = exp(pi*sqrt(2*x/3))/(4*sqrt(3)*x).

1. Rounding F(p(n)) to the nearest integer gives n for every n >= 10.
2. Its only failures on n >= 2 are 2, 3, 4, 5, 7 and 9; at each it gives n-1.
3. Ceiling(F(p(n))) = n for every n >= 2.
4. The bias d_n = n-F(p(n)) has sharp unattained infimum
   delta = 1/24 + 3/pi^2. Its unique maximum is at n=2 globally,
   and at n=11 on n>=10.
5. These extrema determine all successful constant shifts, a unique minimax
   shift, and a two-candidate inverse-staircase formula with one partition comparison.
6. Two convergent inverse correction series have explicit remainder bounds.
   A separate arithmetic exponential expansion identifies the leading parity effect.

The proof uses the classical Rademacher identity, an analytic bound for every
n >= 400, and an exact finite certificate for n=2,...,399. It is not just a
numerical test of many large n. The report is unrefereed, is not formalized in
Lean or Rocq, and does not claim established publication priority.

## Reproduce the exact results

Python 3.10 or newer is sufficient for the syntax. The delivered run used
Python 3.13.5. From this directory:

```sh
python code/certify.py --output results/certificate.json --details results/finite_comparisons.csv
python code/series.py --order 12 --output results/coefficients.json
```

Run the certificate without Python's `-O` flag. Its assertions are proof checks;
the command-line entry point explicitly rejects assertion-disabled execution.

The CSV columns `H_lo` and `H_hi`, divided by `endpoint_denominator`, are lower
and upper endpoints enclosing H(n-shift). The column `relation` states the
strict comparison with the exact integer `p_n`. Every endpoint is an integer;
no floating-point value enters these checks. The file contains a header and
1,204 data rows. The constant bisections are additional checks, not included
in that 1,204 count.

## Reproduce the numerical illustrations

The numerical script requires mpmath. The delivered run used mpmath 1.3.0.

```sh
python -m pip install -r requirements.txt
python code/experiments.py --output results/numerics.json
```

This script uses 130 decimal digits, checks the two coefficient families, and
tests all 4,959 integer targets from 42 to 5000 in the staircase formula.
These calculations are numerical illustrations, not rigorous interval proofs.
The `inverse_12_term_error` is exact model inverse minus truncated approximation.

## Compile the article

A standard TeX Live installation with pdfLaTeX and the packages listed in the
preamble is sufficient. There are no external figures, font files or BibTeX data.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `make pdf`, `make exact`, or `make numerics`.

## Repository and OEIS scope

The ProveIt repository was inspected for mathematical context at commit
`d68b65ea064084fb121df9bb431b21d086f7be81`. It was not modified. No OEIS update
was submitted. A stable public version and independent review would be
appropriate before submitting the enclosed update draft.

The SHA-256 manifest covers the delivered source, PDF, programs, and outputs.
It is an integrity aid, not a mathematical correctness certificate.
