# Source scope and dependency record

## Mathematical inputs

Report146 proves the new all-fixed-order coefficient theorem, its finite scalar
recursion, explicit third order, ratio and logarithmic extrapolation consequences,
and threshold inverses. The independent rate-enclosure section uses only the
Report144 inputs that it states explicitly.

The previously established foundation statements are imported with their proofs:

- Report144: the exact placement recurrence, positivity, the normalized kernel
  bounds, existence and positivity of the radius and rate, boundary divergence,
  the leading pointwise equivalent, and the original rate bracket
- Report145: the second-logarithm starting rate, the critical inverse with its
  boundary condition, and the convergent-series definition of B_2

Both sources and PDFs are included unchanged. SHA-256 values:

- `foundation/Report144.tex`: cf59fa5799913142869a7a79e2b8ec4d04a9c174fdfc7f76d53f86e7d63d44c4
- `foundation/Report144.pdf`: 9397da72116d45aa8e2cda3ef7fa5ebd94989a8ce0a60c7d8fe9dfd7281aa7b9
- `foundation/Report145.tex`: 9e14d0c4797f0387d4441e1e6b4cd751e4d8577f693de640dcdaff63c8769d5b
- `foundation/Report145.pdf`: 59a7f2a3d75852c98c853e4bfa48debedba5c4b942809944e19c507950ec18e9

## External source context

The primary model is Alessandro Serra, *The Number Challenge: Asymptotic Analysis
and Hidden Constant of a Recursive Placement Game*, version 1, manuscript dated
July 22, 2026, published August 15, 2026, Zenodo record 21946055:
https://doi.org/10.5281/zenodo.21946055

The recurrence is Theorem 3.12, equations (47)--(48), printed pages 23--24, as
inspected and documented in Reports144 and145. The original PDF is not redistributed.

OEIS association: https://oeis.org/A398540
A398540 concerns digits of the limiting rate, rather than the rational probability
sequence W_n. Report146 makes no numerical evaluation or universal priority claim.

Robbins' factorial bounds used by the foundation are documented in H. Robbins,
*A remark on Stirling's formula*, American Mathematical Monthly 62 (1955), 26--29:
https://doi.org/10.2307/2308012

## Proof and computation boundary

The analytic uniform estimates, convergence of moments, fixed-order induction,
and first-crossing bounds are mathematical proofs in the article. The companion
is newly written exact finite algebra and validation code. It neither imports
previous computational archives nor turns finite checks into a proof of an
infinite analytic statement. It supplies no decimal connection constants, new
rate digits, effective all-order remainder constants, or certified integer
thresholds. The computable interval theorem has no total-runtime guarantee and
is not presented as an executed numerical refinement.

The new PDF source uses the conventional article style of the foundation.
The hardened build scripts adapt the already tested clean-build and allowlist
patterns, with the new report name, explicit payload list, and new reproduction
tests. Build-script reuse does not reuse the previous mathematical fixtures.
