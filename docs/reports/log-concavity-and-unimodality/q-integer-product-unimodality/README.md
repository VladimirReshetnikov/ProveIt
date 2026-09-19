# A counterexample and a sharp spacing-three criterion for products of q-integers

Research note, 18 September 2026. Prepared with ChatGPT.

## Main finding

Conjecture 5.4 of Connelly–Ito–Martinez–Shevchenko–Yang,
*Unimodality of q-Fibonomial coefficients for small cases*,
arXiv:2605.12822v1, has a false necessity assertion.

Take r=3, b=2, and six ordinary parameters a_i=2. Then

    (1+q)^6 (1+q^3)

has coefficient list

    [1, 6, 15, 21, 21, 21, 21, 15, 6, 1].

It is symmetric and weakly unimodal, but no a_i is divisible by 3 and
b=2 exceeds 1+sum(floor(a_i/3))=1. The source asserts necessity when
k<=3 OR r<=3, so this example is within its claimed range.

The report goes substantially beyond the isolated counterexample:

* It proves the proposed sufficient condition for every r>=2.
* Without an r-divisible ordinary factor, it proves the necessary degree
  bound b<=1+floor(sum(a_i-1)/r).
* It completely classifies spacing two and spacing three.
* For r=3 with no divisible factor, the exact bound is
  b<=1+Q+2*floor(t/6), where Q=sum(floor(a_i/3)) and t counts a_i=2 mod 3.
  Failure gives an explicit first-half coefficient difference equal to -1.
* It proves (1+q)^n(1+q^r) unimodal exactly when n>=r^2-3, for r>=2 and n>=0.

All infinite statements have self-contained algebraic proofs in report.pdf.
This does not settle the source's main q-Fibonomial unimodality conjecture.
The work is not refereed or proof-assistant verified; historical priority
has not been established exhaustively. The exact counterexample itself
can be checked from its ten coefficients.

## Files

- `report.tex`, `report.pdf`: source and compiled research report.
- `verify.py`: standalone exact verifier and reusable polynomial routines.
- `certificate.json`: explicit small counterexample and its parameter checks.
- `verification_results.json`: recorded full test results and experiment ranges.
- `r3_binomial_thresholds.csv`: sharp spacing-three thresholds for b=1..40,
  with a unit-drop witness for the preceding exponent.
- `verify.wl`, `wolfram_output.txt`: input and output of an independent
  Wolfram Language kernel check, actually executed through the connector.
- `PROVENANCE.md`: precise source, scope, and search limitations.
- `Makefile`: build and verification commands.

## Reproduce the exact checks

Python 3.10+ is sufficient; no third-party packages are required.

```sh
python3 verify.py --full --out verification_results.json
```

The script writes the JSON summary, counterexample certificate, and CSV table.
It uses arbitrary-precision integers throughout and raises an exception on
failure. Its checks remain enabled under `python -O`.

A quick smoke test, without overwriting the recorded full results:

```sh
python3 verify.py
```

The recorded full run includes 30,539 exhaustive spacing-three products,
30,000 separately seeded random spacing-three products, 2,000 divisible-factor
cases, 20,000 general-spacing bound checks, and the additional checks listed
in the report. All passed. Within the exhaustive spacing-three collection,
938 cases violate the original necessity condition. These are finite checks,
not substitutes for the proofs.

The function `r3_data(a, b)` implements the exact closed-form decision and
returns the specified coefficient-drop index when the answer is negative.
For example:

```python
from verify import r3_data, product

print(r3_data([2]*6, 2))  # unimodal; exact upper bound on b is 3
print(r3_data([2]*5, 2))  # nonunimodal; drop index is 4
print(product([2]*6, 2, 3))
```

## Rebuild the PDF

```sh
make
# or:
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

A standard TeX Live installation with the packages in the source preamble
is needed. The report uses New PX text/math and Source Sans Pro through
TeX packages; no font files are included in this archive. The bibliography
is embedded in the TeX source, so no BibTeX run or separate .bib file is needed.

The optional independent Wolfram check can be evaluated using
`Get["verify.wl"]` in a Wolfram Language kernel. It is not required to run
any of the Python checks or compile the report.
