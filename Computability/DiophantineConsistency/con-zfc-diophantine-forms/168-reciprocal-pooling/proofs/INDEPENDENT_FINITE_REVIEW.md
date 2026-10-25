# Independent finite algebra review

Review date: 25 October 2026. This is an internal AI-assisted review, not an
external human peer review or a formal-assistant kernel certificate.

## Result

The complete new finite chain from the supplied 225-integer source to the
protected 218-integer quartic and then to the 215-integer decic passes exact
coefficient verification. The independently written checker uses only the
Python standard library and imports no producer, optimizer, or upstream
checker implementation.

The final quartic has 218 integer variables, 155 quadratic residuals, 34,984
collected monomials, and maximum absolute coefficient 113,304. Its equation
file has SHA-256
`878d2f427a117f35b4c211a223003978d52509acc46a5c97b829380b6e608ad8`.

The final decic has 215 integer variables, 152 residuals, maximum residual
degree five, total degree ten, 99,914 collected monomials, and maximum
absolute coefficient 113,304. Its equation file has SHA-256
`a335e0d1d1d82aa2cd30c2f436ed61a752fff001db134b339c23fae01d4a70b0`.

Every declared coordinate occurs in the collected polynomial. The complete
sum of squared residuals was expanded independently and compared with every
delivered coefficient, rather than only with sampled values or hashes.

## Five quadratic projections

For each of the five 225-to-220 steps, the checker constructs the integer
polynomial lift from the stated deleted-row section and checks all source
residuals after substitution. It also checks both map identities. The
projection of the lift is the identity on the new coordinates. In the
opposite composition, each coordinate difference is an explicit integer
multiple of the selected old residual. The old residuals are reconstructed
from the new residuals and the selected residual by exact polynomial
identities. Consequently the stated maps give bijections of integer zero
sets, and the surviving residuals remain quadratic.

Seven deliberate changes were rejected, including a changed quadratic
source term with a refreshed input digest. Thus the checks test algebraic
identities, not only stale-file detection.

## Two affine projections

For 220-to-219 the exact row combination is checked to be affine. The
complete integer affine maps parameterize its hyperplane: the lift lands
on that hyperplane, the projection after lift is the identity, and the
opposite composition differs from the identity by scalar multiples of the
proved affine consequence. Every retained source residual pulled back by
the lift equals its output residual coefficient by coefficient.

The omitted source row need not vanish identically under the lift. It is
recovered from the nonzero coefficient it has in the affine row
combination, once the retained rows vanish. In this instance the omitted
row equals another retained row on the hyperplane. No omitted-row identity
stronger than this was assumed.

For 219-to-218 the checker verifies the row combination, the exact common
content of the affine coefficients, its unit pivot after normalization,
the integer restoration formula, and all substitution and inverse
identities. The unrestricted-integer domain is retained throughout.

The two affine audits reject six and five deliberate corruptions,
respectively, including changed maps and an output coefficient changed
with its digest refreshed.

## Protected residual basis

All 669 elementary integer row operations are replayed, and their inverses
in reverse order recover the entire source residual list. Each operation
has distinct source and target rows and an integer multiplier.

The four pool rows are protected: none is ever used as an operation's
source or target, and all four remain byte-equal to their rows before the
reduction. This removes the need for an additional semantic correction
when the reciprocal-pooling theorem is applied to the final quartic.

## Reciprocal-pooling compilation

For each pool the checker verifies the literal private-coordinate forms,
the identity

`E_j - T_j L_j = norm_j + n_j aggregate_j`,

and `T_j=2A n_j-n_j^2-1`. It verifies that the two bases differ by one, that
the same polynomial `2A` is used, and that all four deleted coordinates
occur only in the four deleted pool rows. It then reconstructs the complete
new residual

`E_0 T_1 + E_1 T_0 - z T_0 T_1`,

checks its complete coefficient list, verifies the coordinate reindexing,
and checks every retained row and the full collected sum of squares.
Seven deliberate corruptions are rejected, including a falsely private
coordinate with an updated input digest.

## Scope

The finite proof for the 218-integer quartic is an exact transport of the
supplied 225-integer source's zero-existence predicate. The 215-integer
decic additionally requires the unbounded reciprocal-pooling arithmetic
theorem and the inherited Pell-frame facts. Those semantic premises are
reviewed separately; the finite checker does not infer them from hashes or
bounded experiments.

This review does not prove consistency, search for a solution, establish
global minimality, recompile the full inherited Lean/Rocq development, or
independently reconstruct all of the parent proof-calculus calibration.
Normal Python and optimized Python runs of the final reciprocal audit
agree, and all checks use explicit exceptions rather than `assert`.
