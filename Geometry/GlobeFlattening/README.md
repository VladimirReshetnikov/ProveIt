# Almost-everywhere globe flattening

Lean proves the main flattening theorem as
`GlobeFlattening.exists_globe_flattening`. For every positive tolerance, it
gives a homeomorphism of the cut unit sphere onto a bounded open planar
domain. The result includes the strict area bounds, the exact area of the
good image, the classical isometric differentials of the map and its
inverse, and the uniform bound relative to the sinusoidal projection. It
also proves positive exceptional image area in every nonempty open target
patch and rules out a Lipschitz bound on any nonempty relatively open
source patch. [Lean theorem](Lean/GlobeFlattening/FlatteningTheorem.lean)

The Lean construction uses continuous monotone staircases with derivative
zero almost everywhere. One sequence approximates longitude, and rescaling
it by `Yₙ(y) = Xₙ(2y) / 2` gives the latitude sequence. Each longitude
approximant sums scaled copies of the Cantor distribution function. The
distribution comes from the binary digits of a uniform point in `[0, 1)`,
read in base three after replacing each `1` with `2`. The digit encoding
is injective, so the distribution has no atoms and its distribution
function is continuous. Scaling the Cantor set by three gives the union
of two translates of the set, forcing its Lebesgue measure to be zero.
The distribution function is locally constant off the Cantor set, so it
has derivative zero almost everywhere.
One induction on the number of translates proves the range, upper plateau,
and one-step error bound for the staircase approximants. Affine rescaling
carries those estimates to the desired interval.
The scalar coordinate is a uniformly converging series of longitude
staircase increments weighted by shifted latitude cosines. On the chart,
telescoping the product differences gives the sinusoidal coordinate plus
a correction with positive weights, yielding a strict slope bound on every
nontrivial horizontal interval. Comparing each weighted staircase with the
clamped identity gives the uniform approximation estimate. The geometric
staircase error bound already gives an initial latitude profile error of
`δ / 8`. Since the absolute longitude is at most `π ≤ 4`, its contribution
is at most `δ / 2`. The two formulas bound
horizontal and vertical errors by increments of the same staircase sum,
with latitude rescaled, giving the joint derivative. The Stieltjes measure
of that sum is the sum of the individual singular measures, so the control
function also has derivative zero almost everywhere. Longitude and doubled
latitude pull back that same derivative event to the chart. Scaling the scalar
tolerance by `1 / (1 + π)` gives a uniform distance bound of `ε` for the
constructed map.
[Scalar construction](Lean/GlobeFlattening/ScalarConstruction.lean) ·
[Singular staircases](Lean/GlobeFlattening/SingularStaircase.lean)

The sphere chart recovers longitude from the complex argument of the
horizontal projection and latitude from the arcsine of height.
[Sphere chart](Lean/GlobeFlattening/SphereChart.lean)

Strict row increase gives injectivity on the closed coordinate rectangle.
Compactness makes the map an embedding, and the interior maps onto the
open region between the continuous longitude endpoint curves. Its image
under the planar coordinate equivalence is the Euclidean target. Mathlib's
formula for the area between the endpoint curves gives the width integral
after swapping coordinates. The strict width comparison proves total area
excess. For local exceptional area, the proof pulls the open target patch
back to coordinates, picks a rectangle there, and applies the same formula
to its image.
The reference cosine integral is the length of the interval swept out by
`2π sin(latitude)`, by the same Jacobian formula applied in one dimension.
The uniform projection error bounds the total area from above.
[Chart homeomorphism](Lean/GlobeFlattening/TriangularChart.lean)

The inverse derivative is the isometric lift into the plane perpendicular
to the radius. Its left inverse is orthogonal projection followed by east
and north coordinates. Applying it to the differentiated inverse identity
gives the forward derivative along the cut sphere. The same inverse
identity gives the injectivity used to prove that the good and exceptional
images are Borel.
[Differential proof](Lean/GlobeFlattening/SphereDifferential.lean)

Spherical area is defined in the longitude–latitude chart with density
`cos(latitude)`, as in the report. The exceptional set also has zero
two-dimensional Hausdorff measure by Lipschitz continuity of the sphere
parametrization. The isometric inclusion of the cut sphere transfers this
nullity to its own metric. A local Lipschitz bound would then give zero
planar area for the exceptional image on an open target patch,
contradicting the local area result. [Spherical area](Lean/GlobeFlattening/SphereMeasure.lean) ·
[Local distortion](Lean/GlobeFlattening/SphereLocalExcess.lean)

Build from the repository root with `lake build GlobeFlattening`.

The delivered [report](globe_flattening_verification.pdf) and
[LaTeX source](globe_flattening_verification.tex) are preserved.

The delivered [README](README.txt),
[original claim](original_claim.md), and figures are retained alongside the
report. The incoming archive was recorded in commit `e270ff954f`.
