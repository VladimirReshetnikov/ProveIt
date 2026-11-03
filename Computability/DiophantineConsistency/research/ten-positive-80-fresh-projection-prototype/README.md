# Positive fresh main-root projection

`TenPositive80FreshProjection.graph_fresh_projection` derives, from an
actual positive 80-graph zero and the symbolic β/low/high ports, a shared
r, positive fresh η and ζ satisfying the unscaled first/main interval
identities, and a positive natural γ such that

    xcoord(2r+1, a) = X + a*C + (4a+3)*γ,
    a = Y*(X+1),  C = ycoord(2r+1, a).

It uses the graph theorem `X = 2^R`, `R = 2r+1`, and one successor step
of the generic nonnegative Pell projection. The predecessor ordinate is
positive because r is positive, so γ is strictly positive. X, Y and R are
from the actual graph, while C, η, ζ and γ are freshly constructed source
quantities. No old graph factor has yet been bound to this identity, and no
source converse, halt equivalence, PDF binding, or iPRA proof is claimed.

The guarded check `observations/fixeddigits-attempt01/` produced
`/tmp/tenpositive-80freshprojection-hpbsxea9/Direct80FreshProjection.olean`,
SHA-256 `c9cc80175e2705b9aa49d6c9a7a6b15d092a7755120852c911e60d98b7d073d6`.
Its receipt records selected direct input pins and resources, with inherited
project/package, dynamic-library and transitive source-object limitations.
