# Explicit height-one quartic for the Con(ZFC) program

This folder gives a complete ordinary integer polynomial with 7,431
variables, degree 4, 34,086 nonzero monomials, and coefficients exclusively
in {-1,+1}. Its constant coefficient is 1. It is separately quadratic in
every variable and nonnegative over the reals.

Its zero set is in a proved explicit bijection with the supplied centered
519-variable direct C222 system. The source's ordinary Con(ZFC)
calibration is inherited from the pinned Round14 incoming archive.
The compiler theorem and full proof are in `PROOF.md`.

## Reproduce

```sh
python3 build.py
python3 verify.py --receipt output/VERIFY.json
python3 -O verify.py --receipt output/VERIFY_OPTIMIZED.json
```

Only the Python standard library is needed. The source SHA-256, immutable
repository commit and archive SHA-256 are in `source/PROVENANCE.json`.

## Exact equation format

`output/polynomial.json` is the complete equation. Its `terms` array has
entries `[coefficient, [variable_indices...]]`, and an entry represents
`coefficient * product(x[i] for i in variable_indices)`. Indices are
zero based; repeated indices indicate powers. The empty index list is
the constant monomial. The equation is the sum of all listed terms = 0.
All variable indices lie in 0,...,7430; every variable is an unrestricted
integer. The `variables` array gives the exact occurrence provenance.
The auxiliary `metrics` field is descriptive and is not part of the
polynomial's definition.

`output/certificate.json` contains the exact normalization and wiring.
`verify.py` reconstructs 2P independently as the sum of squares in the
proof and checks every collected coefficient. The verifier does not
import `build.py` or any upstream builder.

## What is improved

Coefficient height 1 is the least possible positive coefficient height
for any nonzero integer polynomial. The source and previous height-two
compiler have fewer variables; this result optimizes a different metric.
It makes no global simplicity or worldwide-priority claim. There is no
new complete Lean/Rocq or object-ZFC derivation in this folder.

The supplied source proof excerpt and source calibration are inherited
research, not results established by a finite execution of the checker.
The current compiler itself is self-contained finite algebra.
