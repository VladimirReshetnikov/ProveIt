# Small-prime congruences for OEIS A348410

**Article:** `article.pdf` (22 pages), with editable source `article.tex`.
**Date:** 19 September 2026.

## Main outcome

For `a(n) = [x^n] ((1-x)(1-x^2))^(-n)`, the article proves

    v_p(a(m*p^r) - a(m*p^(r-1))) >= 3*r - v_p(12)

for every prime p and all positive m,r. Consequently

    (12/n^3) * sum_{d|n} mu(d)*a(n/d)

is a nonnegative integer for every positive n. The common denominator 12
is optimal: the unscaled transform equals 2/3 at n=3 and 5/4 at n=4.

The principal extension developed here is an exact binary leading-defect
formula for the full integer-parameter family

    A_{alpha,beta}(n) = [x^n](1-x)^(-alpha*n)(1+x)^(-beta*n).

For odd m and r>=2,

    A(m*2^r)-A(m*2^(r-1))
      = 2^(3*r-3)*alpha*beta*binomial((alpha+beta+1)*m-1,m-1)
        modulo 2^(3*r-2).

Generalized binomial coefficients are used for negative upper arguments.
This implies a sharp universal binary modulus 2^(3r-3), and a one-bit
improvement when alpha*beta is even. The general cubic Mobius transform
has common denominator dividing 24, or 12 when alpha*beta is even.

## Source and priority boundary

The initial target was Bala's 2022 OEIS-listed odd-prime conjecture. A
source audit found a prior public proof candidate for it and its full
integer-parameter odd-prime extension. This archive does NOT claim a new
resolution or priority for that result. The prior source is explicitly
credited and pinned in the bibliography and `source_audit.md`.

The prior note expressly did not assert a binary result. The binary defect
formula and denominator-12 completion were not found in the checked
sources. The literature search is not exhaustive and does not establish
global priority. The written proofs are intended to be complete but have
not undergone external peer review or Lean formalization.

The stronger experimental identity
`v_2(a(2^r)-a(2^(r-1))) = 3r+1` for r>=4 is a CONJECTURE here, not a theorem.
It is checked only through r=15 and is not used in any proof.

## Reproduce the exact tests

Python 3.10 or later is recommended. The two exact scripts need only the
standard library and perform no network operations.

```sh
python verify.py
python binary_checks.py
```

The first script allows coverage options:

```sh
python verify.py --max-n 3000 --prime-limit 97 --multipliers 12
python verify.py --help
```

The binary script includes 5,808 checks of the complete leading-defect
formula; 1,936 first-lift checks; 400 exact harmonic-unit checks; 1,000
target denominator/orbit checks; 4,900 general denominator checks; and
290 sharpness/minimal-denominator checks. Its final 78-row exploratory
table is explicitly not a proof of the finer conjecture.

## Optional symbolic and asymptotic checks

```sh
python -m pip install -r requirements-optional.txt
python symbolic_checks.py
```

These check the generating-function elimination and formal series,
saddle constants, Gaussian/Bell formulas for two correction coefficients,
and 90-digit asymptotic comparisons. The symbolic identities are exact;
the comparison table alone uses approximate decimal arithmetic.

## Build the article

Use a normal TeX Live or MiKTeX installation with the packages named in the
preamble. The PDF was built with pdfLaTeX and latexmk.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, `make pdf` builds it, `make exact` reruns the exact checks,
and `make symbolic` runs the optional symbolic checks.

## Files

- `article.tex`, `article.pdf`: complete article, proofs and bibliography.
- `verify.py`: exact evaluator, independent binomial cross-checks,
  odd-prime tests, and boundary counterexamples.
- `binary_checks.py`: binary formula and universal denominator tests.
- `symbolic_checks.py`: optional SymPy/mpmath checks.
- `verification_report.json/.txt`, `binary_report.json/.txt`,
  `symbolic_report.txt`: results of the recorded runs.
- `data/terms.csv`: a(n) through n=1000.
- `data/supercongruence_checks.csv`: odd-prime valuation checks.
- `data/binary_defect_checks.csv`: the full exact binary parameter grid.
- `data/denominator12.csv`: primitive orbits, B(n), 12B(n), and the proved
  orbit divisibility factor through n=1000.
- `data/mobius_invariants.csv`: earlier odd-prime-only orbit checks;
  the stronger completed bound is in `denominator12.csv`.
- `data/binary_valuations.csv`: proved lower bounds beside exploratory
  actual binary valuations, including powers of two through 32768.
- `data/asymptotic_checks.csv`: numerical comparisons at 90-digit precision.
- `source_audit.md`: source URLs, provenance, and priority limitations.
- `oeis_comment_draft.txt`: possible mathematical comments, NOT posted.

All assertion failures raise exceptions. Exact computations use integers
and reduced rational numbers, not floating-point approximations.
