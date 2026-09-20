# The exponential growth constant of OEIS A158415

This archive accompanies `article.pdf` and its LaTeX source, `article.tex`.
It studies the number a(n) of distinct numerical values represented with n
symbols from the grammar

    E ::= 1 | sqrt(E) | (E + E),

with principal square roots. Parentheses do not count as symbols.
Padding a leaf 1 with sqrt(1) shows that exact-size counting equals counting
values whose minimum expression size is at most n.

## Main results proved in the article

- There is a computable constant gamma such that
  `lim a(n)^(1/n) = gamma`, equivalently `a(n) = gamma^(n + o(n))`.
- Certified bounds: `1.86204 < gamma < 1.9208`.
- Exact boundary identity: `sum_{n>=1} a(n) gamma^(-n) = gamma^2`.
  In particular, `a(n) = o(gamma^n)`.
- Explicit algebraic lower and upper bounds, obtained from finite exact
  sequence data, converge to gamma.
- The first 21 OEIS terms are proved exactly by matching independent lower
  and upper certificates. Terms 22 through 28 receive certified intervals,
  not assertions of exact completeness. At n=28 the interval is
  `[1,526,536, 1,526,635]`.

These statements are supported by mathematical proofs and the finite
certificates below. There is no proof-assistant formalization in this archive.
The article does not establish a closed form or sharp decimal value for gamma,
a ratio limit, or an asymptotic equivalent such as C*gamma^n*n^(-3/2).

## Contents

- `article.tex`, `article.pdf`: comprehensive article, proofs, bibliography.
- `certified_enumerate.py`: conservative construction of a lower-bound sample.
- `verify_certificate.py`: independent replay of the expression certificate.
- `certify_upper_bound.py`: rigorous upper convergence certificate and exact
  finite coefficients of the combinatorial majorants.
- `analyze_counts.py`: rational root brackets and the finite-term bounds table.
- `data/digit_sample.bin`: **not distributed** (13 MB). Rebuild with
  `make regenerate`, i.e.
  `python certified_enumerate.py --max-n 28 --precision 256 --output data`.
  It holds 1,526,536 expression DAG records, each assigned a
  formula size at most 28. Sharing compresses storage only; each use of an
  operand is charged again in the formula cost.
- `data/certificate_metadata.json`: generator parameters and output counts.
- `data/verification_results.json`: verifier output, including the exact
  minimum interval gap and the lower-bound inequality.
- `data/upper_bound_certificate.json`: exact signed upper-convergence witness
  and finite upper counts.
- `data/finite_lower_roots.json`: exact rational brackets for finite-alphabet
  reciprocal roots.
- `data/term_bounds.csv`: certified bounds for n=1,...,28.
- `Makefile`: optional convenience targets.

## Verify the shipped certificates

Use Python 3.10 or later. All computation scripts use only the standard
library. Run the following commands from this directory, without `python -O`
(the upper-bound script includes supplementary assertion checks):

```sh
python3 verify_certificate.py --output data/verification_results.json
python3 certify_upper_bound.py --output data/upper_bound_certificate.json
python3 analyze_counts.py
```

Or run `make verify`. The computations require no internet connection or
computer-algebra system. Loading and sorting over a million integer intervals
can require several hundred megabytes of memory.

The sample verifier recomputes all formula costs and dyadic interval enclosures
with 256 fractional bits, then verifies that the intervals are pairwise
strictly disjoint. It also verifies the lower-root inequality with exact
rational arithmetic. Decimal displays are for readability only.

The upper-bound script evaluates a sufficient convergence inequality at the
exact radius `1250/2401`, using outward-rounded integer arithmetic with 1024
fractional bits. Every infinite tail has an explicit proved bound. The upper
endpoint of the resulting convergence witness is negative; it is approximately
`-8.442263650713085e-6`.

The lower certificate by itself proves only the existence of its distinct
sample values. Overlapping intervals are discarded conservatively by the
generator, never treated as proof of equality. Matching this lower sample with
the independent upper majorant establishes completeness only through n=21.

## Regenerate the sample

```sh
python3 certified_enumerate.py --max-n 28 --precision 256 --output data
python3 verify_certificate.py --output data/verification_results.json
python3 certify_upper_bound.py --output data/upper_bound_certificate.json
python3 analyze_counts.py
```

Or run `make regenerate`. This overwrites the generated data files. The
mathematical lower-bound construction needs only the resulting sample, not
an assumption that it exhausts all possible values.

## Build the PDF

A normal TeX Live or MiKTeX installation with pdfLaTeX and the packages listed
in `article.tex` is sufficient. No external bibliography processor is needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run `make pdf`. The PDF is already included. No font files are distributed.

## Binary certificate format

The first eight bytes are the ASCII string `A158415D`. Two little-endian
32-bit unsigned integers follow: precision and maximum assigned symbol cost.
Each record is nine bytes in the Python struct format `<BII`: cost, left child,
right child. The sentinel `0xffffffff` is not a child index.

The first record is `(1, sentinel, sentinel)` and represents 1. A subsequent
record with a sentinel right child is a radical; otherwise it is a sum. All
children must precede the record. The verifier validates all costs and indices
and derives the intervals itself rather than trusting stored approximations.

## Source and date

OEIS definition: https://oeis.org/A158415
Original numerical-equality discussion: https://oeis.org/A158415/a158415.txt
The article includes the complete bibliography and was prepared on
September 20, 2026. The proofs and certificates concern the mathematical
definition, not the accuracy of any unverified sequence extrapolation.
