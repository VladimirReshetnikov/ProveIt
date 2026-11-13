# Independent source review: discrete ordered-ring n=3 scalar obstruction

Source SHA-256 `34df7521dde86dc49d44552fe99bddcc2e970cb98815a34bc5e5ea1a6c6f3f64`. The mathematical argument is valid with its explicit assumptions; no Lean was run. The generic lower and upper endpoint providers were independently result-audited before this review.

For X≥32,Y≥1 and the two strict inequalities `kY<c<k(Y+1)`, assuming `2Y≤X²+4X+4` supplies a nonnegative slack W and contradicts the lower endpoint. The checked upper endpoint yields `2Y<X²+4X+8`, hence `4<Z=2Y−X²−4X<8`. Under X=q·w,Y=q³·s, exact ring algebra gives `Z=qT`, with `T=2q²s−qw²−4w`. Since q≥32 and Z>0, T>0; the explicit discreteness condition `∀z, 0<z→1≤z` gives T≥1, so Z≥q≥32, contradicting Z<8. This does not assume w,s nonnegative: all are ring variables and the separate X,Y inequalities remain explicit.

The result is generic arithmetic in a discrete linearly ordered commutative ring with the explicit hdisc hypothesis; no Pell recurrence, graph zero, fixed ports or 74/75 equivalence is asserted. `simp` with k/c definitions, ordered-ring instances and `linarith`/cast elaboration and the two separate producer closures require guarded Lean and prelaunch reconciliation. It must not be applied to an arbitrary dense ordered ring or to a model until its ordered difference-ring discreteness and required casts are supplied.
