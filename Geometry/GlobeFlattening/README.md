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

The Lean construction uses two sequences of continuous monotone staircases
that approximate longitude and latitude and have derivative zero almost
everywhere. The longitude correction has positive weights, giving a
strict lower bound on the slope of every nontrivial horizontal interval.
Summation by parts gives a second expression for the
same function. Together the two expressions bound horizontal and vertical
errors and give the joint derivative.
[Scalar construction](Lean/GlobeFlattening/ScalarConstruction.lean) ·
[Singular staircases](Lean/GlobeFlattening/SingularStaircase.lean)

The triangular chart is open because it maps open rectangles to regions
between continuous longitude endpoint curves.
[Chart homeomorphism](Lean/GlobeFlattening/TriangularChart.lean)

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
