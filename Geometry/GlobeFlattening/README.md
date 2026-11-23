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

The construction chooses a square mesh at each stage. The slope at the
latitude midpoint plus one mesh width majorizes the target slope across
each row and its interpolation layers. The error inside an old affine
tile controls the difference quotient at every sufficiently nearby point.
Spherical area is defined in the longitude–latitude chart with density
`cos(latitude)`, as in the report. [Scalar construction](Lean/GlobeFlattening/ScalarConstruction.lean) · [Spherical area](Lean/GlobeFlattening/SphereMeasure.lean)

Build from the repository root with `lake build GlobeFlattening`.

The delivered [report](globe_flattening_verification.pdf) and
[LaTeX source](globe_flattening_verification.tex) are preserved.

The delivered [README](README.txt),
[original claim](original_claim.md), and figures are retained alongside the
report. The incoming archive was recorded in commit `e270ff954f`.
