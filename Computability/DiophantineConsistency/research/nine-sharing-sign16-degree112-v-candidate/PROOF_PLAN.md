# Candidate route to a nonnegative V lift

This is a proof plan, not an established model theorem. The candidate deletes
sign17 coordinate 17, whose defining row is

```
v17 = (v5 + 1)^2 * v16 - c,
```

where `c = ((v11 + 1) + (v12 + 1)) * Y + (v11 + 1)` and
`Y = (v8 + 1) * (beta * (v1 + 1) + 1)^3`. The retained cTminusR row
identifies `v16` with `c*T - R`, where `T = v7 + 1` and R is the
window expression. Hence, in a difference ring, the proposed signed lift is

```
(v5 + 1)^2 * c * T - ((v5 + 1)^2 * R + c).
```

The only other occurrence of coordinate 17 in the old seed is squared in Na.
For naturals `X = (v5+1)^2*c*T` and `Z = (v5+1)^2*R+c`, the checked lemma
`Sign33AbsDiffSquare.absdiff_sq X Z` identifies the square of `absdiff X Z`
with the square of the signed difference. This provides a possible way to
recover the auxiliary norm without first establishing the missing sign.

A possible formal sequence over models of IΣ₁ is:

1. Introduce the shifted original coordinates `w j = v(j+1) + 1` for the
   first fourteen coordinates. Establish the port bounds and positivity
   hypotheses required by `Sign33Windows.windows_from_maintained_norms`.
2. Extract the transport, first norm, main norm, strict norm and auxiliary
   norm from the retained Nt, N0, Dc2, scaled_Ns and Na residuals. The first
   norm uses the retained natural tau coordinate; the cTminusR residual
   provides the retained inner coordinate. Derive the auxiliary norm with
   the absdiff-square identity, without a natural V witness.
3. Apply `windows_from_maintained_norms` to derive the half-window `2*R<c`.
   Then apply `Sign33InnerVRing.inner_v_of_window_and_strong` to obtain
   nonnegativity of `f²*(c*T-R)-c`, and use `nonneg_iff` to choose a natural
   representative. Transfer each residual and assemble both zero directions.
4. Specialize to the current symbolic ports only after their model bounds are
   checked; then compose with the independently audited sign17 endpoint.

Each extraction and the cast/monus identifications in steps 1–3 remain to be
proved. In particular, the hypotheses of the window theorem must be obtained
from the reduced equations, not from an assumed original zero or V witness.
The existing named lemmas provide ingredients but do not establish that these
candidate rows supply their premises. The external degree calculation is
independent of this open bridge.
