# Forty-nine-variable quartic candidate

This exploratory 185-operation graph starts from the 50-variable rank-seed
candidate and replaces its two positive coordinates for the signed value `Q`
with a single positive `Q` coordinate, removing the subtraction gate. The
strong-square residual suggests the needed positivity: at a zero it forces
`Q` to be the square of a positive scaled-index variable. The fixed-port
rank-seed reduction and the direct-`Q` reduction require separate model proofs
and a coherent composition.

`generate.py` constructs the graph from the pinned parent and checks gate and
input liveness. `verify_degree.py` expands the 35 residuals as exact sparse
polynomials and checks degree four after the positive shift. The leading
quadratic residual coefficient is port-independent and nonzero. This degree
calculation is external to Lean.

**Open:** the combined 49-variable graph is not yet bound to a Lean literal,
and no combined zero-set equivalence, native iPRA endpoint or guarded proof
replay has been established. No global minimality claim is made.
