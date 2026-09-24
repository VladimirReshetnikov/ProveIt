# A counterexample, exact spacing criteria, and a sharp smoothing threshold for products of q-integers

Research note, 18-20 September 2026. Prepared with ChatGPT.

This package is the merge of two independently produced research packages that
attacked the same conjecture and proved the same threshold theorem by different
routes. See `PROVENANCE.md` and Section 11 of the report for which part came
from where.

## Main finding

Conjecture 5.4 of Connelly–Ito–Martinez–Shevchenko–Yang,
*Unimodality of q-Fibonomial coefficients for small cases*,
arXiv:2605.12822v1 (Section 5.2, p. 14), has a false necessity assertion.

Take r=3, b=2, and six ordinary parameters a_i=2. Then

    (1+q)^6 (1+q^3)

has coefficient list

    [1, 6, 15, 21, 21, 21, 21, 15, 6, 1].

It is symmetric and weakly unimodal, but no a_i is divisible by 3 and
b=2 exceeds 1+sum(floor(a_i/3))=1. The source asserts necessity when
k<=3 OR r<=3, so this example is within its claimed range.

The refutation is not a plateau accident. The witness is log-concave, and
`(1+q)^9 (1+q^3)` is a counterexample with a *unique* maximum and strictly
monotone flanks.

## What the report proves

* The proposed sufficient condition holds for every r>=2 and every k
  (Theorem 3.2). This is the half of Conjecture 5.4 the counterexample leaves
  standing, and it is proved, not merely tested.
* Without an r-divisible ordinary factor, the necessary degree bound
  b <= 1+floor(sum(a_i-1)/r) holds for every spacing (Theorem 4.2).
* Spacing two is completely classified: the original condition is exact
  (Theorem 5.1).
* Spacing three is completely classified: with no divisible factor the exact
  bound is b <= 1+Q+2*floor(t/6), where Q=sum(floor(a_i/3)) and t counts
  a_i = 2 mod 3 (Theorem 6.1). Failure gives an explicit first-half coefficient
  difference equal to -1 at a named index.
* The two-shift family is completely classified for every spacing:
  `(1+q)^n (1+q^r)` is unimodal exactly when n >= r^2-3, for r>=2 and n>=0
  (Theorem 7.1). Two independent proofs are given.
* At the threshold, exactly four consecutive coefficients are maximal, and the
  maximizer counts then run 4, 3, 2, 1, 2, 1, 2, ... as n increases
  (Corollary 7.6, and the discussion following it).
* For gap three and every n>=6, `(1+q)^n (1+q^3)` is a *log-concave*
  counterexample (Corollary 7.8); and for every B>=2 and t >= 6*floor(B/2),
  `(1+q)^t [B]_{q^3}` is a counterexample as well (Corollary 6.3).
* Across *all* spacings, the minimum degree of a counterexample is nine, and
  the degree-nine parameter set is unique up to permutation and deletion of
  trivial factors (Proposition 8.1), proved by a complete finite search whose
  completeness is itself proved.

All infinite statements have self-contained algebraic proofs in `report.pdf`.
This does not settle the source's main q-Fibonomial unimodality conjecture.
The work is not refereed or proof-assistant verified; historical priority has
not been established exhaustively. The exact counterexample itself can be
checked from its ten coefficients.

## Deliberate duplications

Table 6 of the report (Section 10.7) lists eleven results, proofs and artefacts that are
kept in more than one copy on purpose, each with a line on what the second copy
buys: two proofs of the threshold theorem, two accounts of the failure one step
below it, two minimality results, two counterexample families, two witness
polynomials, two computer algebra witnesses, five coefficient implementations,
two unimodality tests, two threshold tables on orthogonal axes, two closure
lemmas, and two provenance records (merged here into one file).

## Files

- `report.tex`, `report.pdf`: source and compiled research report (25 pages).
- `code/verify_products.py`: exact verifier and reusable polynomial routines for
  the general product; API includes `convolve`, `q_integer`, `multiply_uniform`,
  `ordinary_product`, `multiply_comb`, `product`, `unimodal`,
  `symmetric_unimodal`, `conjectured_condition`, `r3_data`, `validate_r3`,
  `counterexample_certificate`, `write_tables`.
- `code/verify_threshold.py`: exact verifier for the two-shift family and the
  minimum-degree search; regenerates the CSV and JSON reports in `data/`.
  Disjoint test suite and disjoint API from `verify_products.py`.
- `code/minimal_certificate.py`: standalone independent degree-nine search using
  direct tuple counting rather than polynomial multiplication. Its source is
  typeset verbatim into Appendix B of the report, so the article is
  self-contained as a certificate.
- `code/symbolic_checks.py`: optional SymPy checks of three algebraic identities.
- `code/verify_products.wl`: input of an independent Wolfram Language kernel
  check, actually executed through the connector.
- `data/certificate.json`: explicit small counterexample and its parameter checks.
- `data/verification_results.json`: recorded full run of `verify_products.py`,
  with experiment ranges and seed.
- `data/r3_binomial_thresholds.csv`: sharp spacing-three thresholds for b=1..40,
  with a unit-drop witness for the preceding exponent. (Axis: b.)
- `data/thresholds.csv`: two-shift thresholds for r=2..100, with the exact
  central obstruction immediately below each threshold and the plateau range.
  (Axis: r. Neither table is a subset of the other.)
- `data/degree_search.csv`: every normalized parameter set of degree at most
  nine, all coefficients, and condition/unimodality flags.
- `data/degree_summary.csv`: enumeration counts by degree.
- `data/counterexample.json`, `data/verification_report.json`,
  `data/verification_output.txt`, `data/minimal_certificate_output.txt`,
  `data/symbolic_report.json`: outputs of the two-shift, independent and
  symbolic checks.
- `data/wolfram_output.txt`: returned text of the Wolfram kernel check.
- `data/area_selection.json`: original random area draw and its 24-area list.
- `PROVENANCE.md`: merged source, scope, search and computational audit.
- `Makefile`, `requirements-optional.txt`: build/verification shortcuts and the
  optional pinned SymPy version.

No checksum manifest is distributed with this package, and none should be added.

## Reproduce the exact checks

Python 3.10 or later is sufficient; no third-party packages are required for
the two main verifiers. The two-shift verifier is written for Python 3.9 or
later; the recorded outputs in `data/` were regenerated with CPython 3.14.4
(the two-shift package's original run used 3.13.5). Run from this directory:

```sh
python3 code/verify_products.py --full --out data/verification_results.json
python3 code/verify_threshold.py
python3 code/minimal_certificate.py
```

The first command writes the JSON summary, the counterexample certificate, and
the spacing-three CSV table; it returns a nonzero exit code if any check fails.
A quick smoke test, without overwriting the recorded full results:

```sh
python3 code/verify_products.py
```

The recorded full run of `verify_products.py` includes 30,539 exhaustive
spacing-three products, 30,000 separately seeded random spacing-three products,
2,000 divisible-factor cases, 20,000 general-spacing bound checks, and the
additional checks listed in Table 4 of the report. All passed. Within the
exhaustive spacing-three collection, 938 cases violate the original necessity
condition while satisfying the corrected theorem.

The default run of `verify_threshold.py` checks 3,263 pairs in a rectangular
grid (2<=r<=14, 0<=n<=250), 594 boundary and nearby rows through r=100, 98
central-difference identities, 2,450 exact ratio comparisons, and all 144
normalized parameter sets of degree at most nine, each of which is independently
re-counted by weighted-tuple enumeration (4,762 tuples in total). It accepts
`--help`, `--out PATH`, `--max-shift`, `--degree-bound`, `--grid-max-shift` and
`--grid-max-n`; increasing the degree bound increases the partition enumeration,
while independent tuple checking stays restricted to degrees at most nine.

These are finite checks, not substitutes for the proofs — with the single
exception of the degree-at-most-nine search, whose completeness is proved in
the report.

Optional symbolic verification, with SymPy already installed:

```sh
python3 code/symbolic_checks.py
```

The optional pinned dependency is listed in `requirements-optional.txt`.
No network access is used by any verification program, and all checks remain
enabled under `python -O`.

The function `r3_data(a, b)` implements the exact closed-form spacing-three
decision and returns the specified coefficient-drop index when the answer is
negative. For example:

```python
import sys; sys.path.insert(0, "code")
from verify_products import r3_data, product

print(r3_data([2]*6, 2))  # unimodal; exact upper bound on b is 3
print(r3_data([2]*5, 2))  # nonunimodal; drop index is 4
print(product([2]*6, 2, 3))
```

## Rebuild the PDF

```sh
make
# or:
latexmk -pdf -interaction=nonstopmode report.tex
latexmk -c report.tex
```

A standard TeX Live or MiKTeX installation with the packages in the source
preamble is needed. The report uses New PX text/math and Source Sans Pro
through TeX packages; no font files are included in this archive. The
bibliography is embedded in the TeX source, so no BibTeX run or separate `.bib`
file is needed, and no shell escape is required. Keep
`code/minimal_certificate.py` in place: Appendix B typesets that file directly.

The optional independent Wolfram check can be evaluated using
`Get["code/verify_products.wl"]` in a Wolfram Language kernel. It is not
required to run any of the Python checks or to compile the report.
