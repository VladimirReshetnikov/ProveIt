# Smaller Diophantine forms of ZFC consistency

Prepared 22 October 2026 for ProveIt, using snapshot
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

This package combines the raw-K215 blank coefficient recipe of `06-blank67`,
the ordinary strong Pell equation used by `02-system63`, and the quadratic
register elimination of `08-start-only67`. It also proves a new reduction
of the positivity requirements, leading to 29 unrestricted integer variables.

## Results

| Form | Domain and unknowns | Equations | Exact degree | Arithmetic operations |
|---|---|---:|---:|---:|
| Ordinary system | 15 positive integers | 6 | Maximum 28 | 61 = 34M + 27A |
| Ordinary product | 15 positive integers | 1 | 99 | 69 = 39M + 30A |
| Ordinary SOS | 15 positive integers | 1 | 56 | 78 = 40M + 38A |
| Quadratic lift | 33 positive integers | 24 | Maximum 2 | Not compared |
| Quartic SOS of lift | 33 positive integers | 1 | 4 | Not compared |
| Integer system | 29 unrestricted integers | 6 | Maximum 50 | 113 = 57M + 56A |
| Integer ordinary product | 29 unrestricted integers | 1 | 188 | 121 = 62M + 59A |
| Integer ordinary SOS | 29 unrestricted integers | 1 | 100 | 130 = 63M + 67A |
| Integer normalized product | 29 unrestricted integers | 1 | 300 | 119 = 62M + 57A |
| Integer reduced product | 29 unrestricted integers | 1 | 236 | 120 = 62M + 58A |

`M` counts binary multiplications; `A` counts binary additions/subtractions.
Fixed numerals are free, but arithmetic with a fixed numeral is charged.
System equality comparisons are not arithmetic operations.

For each formulation ZFC proves that lack of solutions **in the stated
domain** is equivalent to Con(ZFC). This is an ordinary mathematical proof
using the pinned K215 calibration and native-window compiler. The new
Diophantine bridge is not formalized in Lean or Rocq. No consistency proof,
global optimality result, or new varying-input universal bound is claimed.

The 15-variable degree-28 system improves the previous 16-variable,
seven-equation, degree-28, 63-operation system. It also lowers the degree of
the old 15-variable, six-equation, 61-operation system from 60 to 28.
The degree-99 product costs two more operations than the old 67-operation,
degree-155 product; these are different tradeoffs. The quartic improves
34 positive unknowns/25 quadratics to 33/24. The unrestricted-integer forms
improve the earlier 41-variable explicit versions; 29 is not asserted to
be a global minimum among all known Diophantine representation methods.

## The equations

Use the exact fixed ports `Bm1`, `Kconstant`, `MC`, `MF` from
`vendor/blank67/k215_constants.json`. `MF` is the shifted source coefficient,
not the native field mask. Constants from other packages are not interchangeable.

The main positive variables are
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`.
The report gives a compact closed formula. The JSON files list every gate
as `[new_register, operator, left_operand, right_operand]`; an integer
operand is a literal numeral, and a string is an earlier register or port.
Polynomial packets name one `output`. System packets specify `comparisons`.
The quartic packet gives 24 factored equations and independently expanded
residuals; sum the squares of the residuals to obtain the single quartic.

The 29-integer form retains seven positive coordinates
`J,F,alpha,z,s,eta,zeta`, replacing each by
`1+u*u+v*v+r*(r+1)`. It uses `i=2*i_integer+1`,
`w=w_integer*w_integer`, and leaves `f,h,T,tau,y,gamma` unrestricted.
The report proves why these restrictions preserve completeness and why
the newly allowed signed/zero boundary cases do not create false solutions.

## Reproduce offline

Python 3.10 or later and its standard library suffice for all arithmetic
and finite compiler checks. From this directory:

```sh
python3 src/reproduce.py
```

This checks 47 pinned source hashes, regenerates all nine equation packets
in a temporary directory, compares them with the delivered packets, and
performs the independent circuit, degree, quartic, odd-multiplier, coefficient
layout, local-tableau, and exact alphabet-count audits. The resulting
`VERIFICATION.json` states exactly what was checked.

To rebuild the manuscript, a standard TeX Live installation with the listed
LaTeX packages is needed:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

No test expands the astronomical coefficients (the cell base alone is
`2^(5^67)`), enumerates all `1420903358357108792377` windows, or supplies
an accepting K215 computation. The tests are finite diagnostics and exact
algebra checks, not substitutes for the ordinary mathematical proofs.
The inherited proof-assistant builds are not rerun.

## Files and provenance

- `report.tex`, `report.pdf`: full manuscript, proofs, comparisons, finite
  coefficient definition, formalization boundaries, and further questions.
- `src/`: reproducible generators and verification drivers.
- `data/`: nine emitted equation specifications, receipts, and literal K215 table.
- `proofs/`: detailed new proof notes and independent reviews.
- `vendor/blank67/`: unchanged parent circuits, coefficient recipe, local
  predicate, and finite source-checking code.
- `dependencies/`: selected pinned mathematical proof dependencies and the
  original eight-package reconciliation. Original relative references in
  these unchanged texts refer to their repository locations; use
  `SOURCE_MANIFEST.json` to resolve the copies and pinned source paths.
- `SOURCE_MANIFEST.json`: exact source identities and hashes.
- `licenses/`: inherited MIT-0 source notices.

The repository's full K215 proof-assistant project is an external pinned
dependency; it is not duplicated here. The ordinary compiler proof texts
needed for the new argument are included, with further literature and
repository references retained. All coefficients remain exactly those of
package 06, whose construction was based on
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

New material is offered for incorporation into ProveIt under the same MIT-0
terms as its surrounding repository material. Existing source attribution
and notices are retained. No remote repository modification was made.

