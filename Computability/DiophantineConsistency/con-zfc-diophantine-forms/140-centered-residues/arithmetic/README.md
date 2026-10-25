# Centered remainder certificates for Diophantine consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

The principal equation is the sum of the squares of the **186 quadratic
residuals** in `signed258/equation.json`, with its 258 coordinates ranging
independently over all integers. Its complete collected quartic is in
`signed258/expanded_polynomial.json`. With the explicitly retained numerical
C222/ZF/ZFC calibration, ZFC proves that it has no integer zero if and only
if Con(ZFC).

## Selected exact equations

Every equation below has degree four. A residual term `[c,[i,j,...]]` denotes
the integer coefficient c times the product of the indexed coordinates;
an empty list denotes a constant. Repeated indices denote repeated factors.
All indices are zero based. The polynomial is exactly the sum of the squares
of every listed residual; that notation introduces no new unknowns.

| Directory | Domain | Variables | Rows | Collected monomials | Height |
| --- | --- | ---: | ---: | ---: | ---: |
| `signed258` | unrestricted integers | 258 | 186 | 5,366 | 128,446 |
| `signed259` | unrestricted integers | 259 | 185 | 5,361 | 128,446 |
| `natural222` | nonnegative integers | 222 | 172 | 9,522 | 83,954,186 |
| `natural221_high` | nonnegative integers | 221 | 171 | 10,216 | 2,445,412,949,744 |
| `natural223_sparse` | nonnegative integers | 223 | 173 | 6,858 | 83,953,724 |

`audit261` retains the first isolated radius reduction: 261 integers,
185 rows, 5,377 terms and height 128,446. It is an audit checkpoint, not
an additional selected frontier point.

Compared with the inspected incoming 282-integer equation, the principal
removes 24 variables, six rows and 125 collected monomials, while preserving
degree and coefficient height. The 259-variable companion uses one fewer
row and five fewer terms than the principal. These are exact comparisons,
not global minimum claims.

## Main new arithmetic

The signed source's own radix margins force every canonical low remainder
below one fifteenth of its modulus, before its factorial is interpreted.
A single quadratic radius row can therefore authenticate several signed
remainders and recover their nonnegative orientations. Three shared radius
rows replace eleven old interval-product certificates. An odd-square radix
replaces the old initial output-slack guard, with a reordered soundness
argument and compatible parity choices in completeness.

Read `SIGNED_RADIUS_PROOF.md`, then `ODD_SQUARE_AND_WEIGHTED_PROOF.md`.
`NATURAL_PROOF.md` explains the separate natural-domain pooled-digit branch.
The main signed theorem uses no K215 simulation, Jones universal polynomial,
Sun reduction, or large fixed machine-coefficient tuple.

## Offline exact verification

Python 3.10 or later and its standard library are sufficient. From any directory:

    python3 -B /path/to/arithmetic/verify.py
    python3 -B -O /path/to/arithmetic/verify.py
    python3 -B /path/to/arithmetic/verify.py --rebuild

The checkers independently reconstruct every new raw residual, inspect the
full private-coordinate deletion boundary, replay every monic projection and
translation, and collect every final polynomial coefficient. Corruption
controls must fail. The optional rebuild compares all selected generated JSON
bytes against fresh temporary reconstructions. It does not modify the release.
Use `--receipt /path/out.json` to save a new receipt outside a sealed copy.

Component commands are `verify_signed.py --negative-controls` and
`verify_natural.py --negative-controls`. The former imports no new producer;
the latter independently checks the natural source mutation and every
nonnegative restoration certificate. Finite checks certify exact algebra,
not unbounded arithmetic or consistency.

## Complete retained source boundary

`upstream/round17/direct/` and `upstream/round17/architecture/` retain the
ordinary proof dependencies, literal source data, constructor code, licenses,
and calibration interface sources from the inspected incoming round-17
package. In particular, the C222 and ZF/ZFC interfaces are present under
`upstream/round17/architecture/proofs/inherited/calibration/`.
The whole transitive Lean development was not rebuilt; this contribution
does not claim a new end-to-end Lean/Rocq or encoded object-ZFC derivation.

`source/` and `signed_source/` are exact local inputs for the new portable
builders. Their source identities are recorded in `PROVENANCE.json`.
`vendor/` contains the credited independent algebra and projection tools.
No repository branch, issue, or external publication was changed.

There is no proof of either Con(ZFC) or its negation here. The result is a
proved equivalence, formalizable in ZFC, between syntactic consistency and
unsolvability of each explicitly supplied polynomial in its stated domain.
