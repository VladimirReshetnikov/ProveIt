# A proof of the generating function for OEIS A199085

## Result

For the number a(n) of distinct third derivatives at x=1 among all
fully parenthesized exponentiation expressions with n copies of x,

    a(1) = a(2) = 1,
    a(n) = floor((n^2 - 2)/3)  for n >= 3.

The ordinary generating function (starting at n=1) is

    sum_{n>=1} a(n) z^n
      = z/(1-z) + z^3/(1-z)^3 - z^7/((1-z)^2 (1-z^3))
      = z (z^6 - 2z^4 - z^2 + z - 1)
          / (z^5 - 2z^4 + z^3 - z^2 + 2z - 1).

The article gives a self-contained proof for all n, not a numerical
extrapolation. It classifies every attainable pair of second and third
derivatives and constructs witnesses for every admissible pair.

## Contents

- `article.pdf`: the complete mathematical article.
- `article.tex`: editable LaTeX source; no external figure files are needed.
- `verify.py`: exact-arithmetic verification and witness construction.
- `oeis_note.txt`: a compact proof note, prepared for possible use in an
  OEIS contribution; it has not been submitted to OEIS.
- `Makefile`: optional build and test commands.
- `artifacts/verification_report.json`: results from the executed checks.
- `artifacts/state_counts.csv`: joint state counts, overlap corrections,
  and distinct third-derivative counts for 1 <= n <= 60.
- `artifacts/coefficients.csv`: a(n) for 1 <= n <= 1000.
- `artifacts/derivative_states.json`: every distinct pair of actual second
  and third derivatives for 1 <= n <= 60. These are not normalized values.
- `artifacts/witnesses_n5_n7.json`: explicit fully parenthesized expressions
  realizing every joint derivative state at n=5 and n=7.

## Reproduce the computations

Use Python 3.10 or later. No third-party package or network is required.
Run from this directory:

```sh
python3 verify.py --out-dir artifacts
```

On Windows, `python` may be used in place of `python3`.
Do not use `-O`: the verification deliberately relies on assertions and
refuses to run when assertion checking is disabled.

Optional limits:

```sh
python3 verify.py --dp-limit 60 --tree-limit 10 --witness-limit 20 \
  --series-limit 1000 --out-dir artifacts
```

The default executed checks were:

1. Exact recursively computed derivative states equal the classification
   through n=60.
2. Every ordered binary parenthesization through n=10 is evaluated using
   independent rational Taylor arithmetic modulo t^4. This comprises
   6,918 trees in total, including 4,862 at n=10.
3. All 1,160 constructed joint-state witnesses through n=20 have the
   correct number of leaves and the claimed exact Taylor coefficients.
4. The first 1,000 positive-index coefficients of the original rational
   function agree with both the closed formula and the overlap formula.
   The stated recurrence relations are also checked.

Finite checks supplement, rather than replace, the all-n mathematical
proof. The generic Taylor evaluator does not use the derivative-state
composition recurrence.

## Rebuild the PDF

Use a standard TeX Live or MiKTeX installation. The source declares all
required packages, including `newpxtext`, `newpxmath`, `amsmath`, `amsthm`,
`mathtools`, `microtype`, `booktabs`, `listings`, `hyperref`, and `cleveref`.
No separately distributed font files or bibliography database are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error
article.tex` repeatedly until references and the table of contents are
stable (normally two or three passes on a clean build).

`make all` rebuilds both the PDF and the verification artifacts.

## Source and attribution

The problem and proposed generating function are in OEIS A199085:
https://oeis.org/A199085
https://oeis.org/search?q=id:A199085&fmt=text

The entry was consulted on September 20, 2026. It attributes the sequence
to Vladimir Reshetnikov, the conjectured generating function to Alois P.
Heinz (November 2, 2011), and a program evaluating the floor formula to
Vladimir Joseph Stephan Orlovsky (February 1, 2012).

The article's proof is presented independently of the computations. No
claim of an exhaustive priority search, peer review, or proof-assistant
formalization is made.
