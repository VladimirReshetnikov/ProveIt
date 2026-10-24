# Review of the 977-integer quartic

## Scope and conclusion

I reviewed the root-authored `direct/code/build_integer.py`,
`signed_contract.py`, and `verify_integer.py`, together with the literal
`direct/integer977` equation, complete expansion, and elimination certificate
in `output/ConZFC_Constructive_Reductions_2026-10-23`.

**Conclusion: the 170-guard lift and all 28 signed monic contractions preserve
integer solvability. The literal result has 977 unrestricted integer
variables, 533 quadratic residuals, exact degree four, 24,632 collected
monomials, and coefficient height 83,869,250. I found no mathematical or
artifact-level defect in this composition.**

This review is independent of the authoring of these three integer-lift and
contraction files. I previously authored the projected 495-natural source and
the independent domain-certificate checker, so this is not external peer
review of every inherited component.

## Guard equivalence

Each selected natural coordinate x receives precisely the equation

    x = a^2 + b^2 + c^2 + c,

with three new unrestricted integers. Its right side is nonnegative for every
integer triple because c(c+1)>=0. Conversely, if x>=0, the classical
three-square theorem represents 4x+1 by three squares: this number is not of
the forbidden form 4^r(8s+7). Modulo four, exactly one of the three squares is
odd. Writing the odd root as 2c+1 and the other roots as 2a and 2b gives the
displayed representation.

The guard list is exactly the 170 indices in DOMAIN_CERTIFICATE.json; the
checker verifies uniqueness, range, and agreement. Once these guards hold,
the separately checked frame-domain certificate proves all 495 original
coordinates nonnegative. Thus a guarded integer solution is a genuine
natural source solution. Conversely, every natural source solution admits
all 170 independent guard extensions. Keeping the source coordinates while
adjoining the guards is essential to preserving quadratic residual degree.
The intermediate counts are exactly 1005 variables and 561 residuals.

## Signed contractions

A pivot row has the exact form epsilon*(x-P)=0, epsilon in {1,-1}, where P
is an integer polynomial not containing x. Deleting the row and substituting
P everywhere is an existence equivalence over the integers. The inverse
restores x=P after the other coordinates have been restored. The use of
negative coefficients is legitimate here because the domain is unrestricted.

The certificate contains 28 pivots: 11 affine and 17 quadratic restorations.
All 28 include negative coefficients, so their validity must be asserted
after the integer lift rather than as natural-domain contractions. The
independent verifier checks each literal pivot identity, absence of cycles,
use of only live variables, exact substitution into every remaining row, and
quadratic degree after every step. It then verifies the retained-coordinate
ordering and every final residual. No unused free coordinates remain.

## Exact data and replay

I ran the supplied independent integer verifier both normally and with
`python3 -O`. Both passed, including the two corruption controls: an altered
restoration coefficient and an altered expanded coefficient are rejected.
The verifier imports neither the builder nor the contraction implementation.
It independently reconstructs the guards, replays the substitutions, and
collects the entire sum-of-squares expansion.

The coefficient of x_0^4 is exactly 23, providing an explicit attained-degree
witness. Thus degree four is an exact statement, not merely a graph bound.

Reviewed artifact hashes:

| File relative to direct/ | SHA-256 |
|---|---|
| code/build_integer.py | 5709d7ae84628b746c4e9200bd67797205a8a2d218291060bcf95be6b3123548 |
| code/signed_contract.py | 9e0f3d0da4e558e65381f14ab16583549f3cf8fde44f79c76415b930e91a68f9 |
| code/verify_integer.py | 0c9c33d657a46f452d37e9352e17944a480c336ba0cfd0f47db374c5b444c654 |
| integer977/equation.json | 5ee423599ffdd2c1222b17ba50f970b17bc8dc7607757d84f7687259b0f23d34 |
| integer977/expanded_polynomial.json | 185ebf6de4a83a0ad115476e0a334c5f1aeb88ce26db7b7ecf575a31d0f24aa3 |
| integer977/elimination_certificate.json | bada5a5c9495d0eb29390870cb0275ffd61eb063c006b1e5f33f43093ba502c0 |

These checks establish the new finite algebraic reduction. The final
Con(ZFC) interpretation continues to use the separately identified ordinary
calculus calibration and source arithmetic theorems; this review does not
claim a new proof-assistant kernel certificate or a consistency decision.
