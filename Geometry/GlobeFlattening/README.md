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
function is continuous. Support on the null Cantor set makes the
distribution singular, so its distribution function has derivative zero
almost everywhere.
The scalar coordinate is a uniformly converging series of longitude
staircase increments weighted by shifted latitude cosines. On the chart,
telescoping the product differences gives the sinusoidal coordinate plus
a correction with positive weights, yielding a strict slope bound on every
nontrivial horizontal interval. The two formulas bound the horizontal and
vertical errors by increments of the same staircase sum, with latitude
rescaled, giving the joint derivative. The Stieltjes measure of that sum
is the sum of the individual singular measures, so the control function
also has derivative zero almost everywhere. Scaling the scalar tolerance by
`1 / (1 + π)` gives a uniform distance bound of `ε` for the constructed map.
[Scalar construction](Lean/GlobeFlattening/ScalarConstruction.lean) ·
[Singular staircases](Lean/GlobeFlattening/SingularStaircase.lean)

The sphere chart recovers longitude from the complex argument of the
horizontal projection and latitude from the arcsine of height.
[Sphere chart](Lean/GlobeFlattening/SphereChart.lean)

Strict row increase gives injectivity on the closed coordinate rectangle.
Compactness makes the map an embedding, and the interior maps onto the
open region between the continuous longitude endpoint curves. The strict
width comparison proves total area excess. For local exceptional area,
the proof pulls the open target patch back to coordinates, picks a
rectangle there, and uses the same width comparison on that rectangle.
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
parametrization. A local Lipschitz bound would therefore give zero planar
area for its image on an open target patch, contradicting the local area
result. [Spherical area](Lean/GlobeFlattening/SphereMeasure.lean) ·
[Local distortion](Lean/GlobeFlattening/SphereLocalExcess.lean)

Build from the repository root with `lake build GlobeFlattening`.

The delivered [report](globe_flattening_verification.pdf) and
[LaTeX source](globe_flattening_verification.tex) are preserved.

The delivered [README](README.txt),
[original claim](original_claim.md), and figures are retained alongside the
report. The incoming archive was recorded in commit `e270ff954f`.
