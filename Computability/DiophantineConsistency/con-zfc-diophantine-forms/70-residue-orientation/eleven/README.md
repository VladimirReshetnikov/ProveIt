# Eleven positive unknowns: degree 325 in 113 operations

The explicit polynomial `p11_positive_degree325.json` has eleven strictly
positive integer witnesses, exact total degree **325**, and **113** binary
arithmetic operations: 67 multiplications, 29 additions, 17 subtractions.
Its residuals have degrees 312 and 13 and jointly cost 110 operations.
At the pinned ProveIt state, package 52 has degree 954 and 113 operations.
This construction removes 629 degrees while matching the operation count.

The witnesses are `j,F,alpha,i,T,X,Y,n,eta,zeta,gamma`. All other names
are computed polynomial registers. The complete four fixed numerals are
in `coefficients/`; `MF` is already shifted. They are not extra witnesses
or replaceable test values.

Read `section.tex` for the report contribution and `PROOF.md` for the
complete proof. Its weighted first-carrier theorem is proved in the sibling
`../positive/section.tex`, which precedes this section in the combined
report. The normalized positive auxiliary reconstruction and inherited
source assumptions are pinned in `upstream/package61_report.tex`.
The inspected predecessor's proof is retained as
`upstream/package52_Y_ABSORPTION_PROOF.md`.

## What changes

The normalized positive auxiliary reconstruction permits
`V=Df*(c*T-R)-c`. Its radicand is independent of the sign of the strong
Pell root. The first, strong and auxiliary roots therefore enter a direct
octic sum norm while the degree 13 adaptive main equation stays separate.
Multiplying the strong ordinate by `q*(q-1)` makes the auxiliary
denominator coprime to the transport denominator. Rational root recovery
then implies integrality by a direct denominator argument. A positive
polynomial majorant absorbs both signed roots into the first transport
coordinate.

Package 52 already uses conjugate norms, radical separation, positive
majorants, quotient absorption, and unit-product finalizers. The claim is
the specific composition and the 325/113 endpoint, not invention of those
methods or global optimality.

## Reproduce offline

With Python 3 and only its standard library:

```sh
python3 build.py
python3 verify.py
python3 -O verify.py
python3 independent_audit.py
python3 -O independent_audit.py
```

`VERIFICATION.json` and `OPTIMIZED_VERIFICATION.json` are the own-checker
receipts. The independent review and finite audit accompany them. The
exact checker expands sparse integer polynomials and cut contracts; it
does not rely on sampling. It checks the main degree cancellation, the
degree 325 certificate and the coefficient `2^7 * 3^8 * (3*beta)^108` of
`j^108 i^24 eta^49 X^42 Y^85 alpha^16 gamma`.

The conclusion is that lack of positive solutions is equivalent in ZFC
to `Con(ZFC)`. The inherited unbounded native compiler and K215 syntactic
refutation calibration remain ordinary mathematical dependencies. Finite
circuit checks are not a consistency test or an end-to-end formal proof.
