# Positive center from a reverse-carrier balance

`TraceCenterPositive.square_term_lt_n` proves in every supported IΣ₁ model that, for model-natural values,

```text
n+κ = τ*f*y + u²*(b*t) + t + ρ,
τ>0, y>0, κ<f
    imply u²*(b*t)<n.
```

`center_positive` concludes `0<n−u²*(b*t)`. The hypotheses have the same algebraic shape as the balance produced by `TenPositiveReverseCarrier.positive_carrier`; this packet does not import or apply that theorem, identify its `u` and `b*t` with the 75-row trace registers, or construct a reduced graph. It is an ingredient for investigating whether the two rows `LBt=V²*B` and `center=n−LBt` can be replaced by a positive center input in a completeness construction. The opposite direction would still need, among other things, nonnegativity of B on arbitrary zeros of the changed graph; neither a 73-row equivalence nor an iPRA result is claimed.

Guarded author `observations/attempt02/` and its enclosing tool session exited 0. Accepted V2 source SHA-256 is `f2d4f68b46ea459e8738d48aebedccd22882302be26a9e06107786207408457c`; terminal SHA-256 is `1b9f0e79fdf2697af9f07f32fe4ed918c3522d768585c2eedcfa465905067fed`; output `/tmp/trace-centerpositive-0_fb28_g/TraceCenterPositiveV2.olean` SHA-256 is `c1502792816d437971e4fa1fc632a3d78fbaafe89a15925820b11a136c29799e`. Attempt01 failed on add-lemma argument order; its source, runner and receipt are retained. Direct Foundation and Mathlib objects are pinned; transitive package/dynamic ancestry remains inherited, and no independent Lean replay is claimed.
