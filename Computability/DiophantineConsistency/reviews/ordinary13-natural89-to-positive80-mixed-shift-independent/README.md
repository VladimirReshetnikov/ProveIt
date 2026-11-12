# Independent source review: natural 89 to positive 80

This reviews the inert source proposal at
`research/ordinary13-natural89-to-positive80-model-draft/`. No Lean was run;
the proposal is not an elaborated or kernel-checked proof.

The two graph literals regenerate byte for byte from the pinned JSON sources.
An independent symbolic checker then substitutes the exact mixed valuation,
normalizes sums in the free commutative additive group, and represents products
as uninterpreted commutative products of the normalized operands. The two full
graph outputs agree by these valid commutative-ring identities; in particular,
the `k` and `r0` intermediates agree. No multiplication is expanded and no
finite sample is used to infer this equality. As negative controls, omitting
any one of the ten proposed increments makes the normalized graph outputs
differ. These controls detect these specific changed maps; they are not a
uniqueness or minimality result.

The coordinate order is J, F, alpha, f, i, T, w, s, r, eta, zeta, y,
gamma. Positions 3, 8 and 11 (f, r and y) are direct; all ten other
positions are incremented. In particular the positive graph has
`k=(n_eta+1)+(n_zeta+1)`, while the 89 graph writes
`kbase=(n_eta+1)+n_zeta`, `k=kbase+1` and `r0=kbase-R`; these are the
same ring expressions as the positive graph's `k` and `r0=k-R-1`.

At the mathematical statement level, a zero of `positiveShift positive80`
raises every coordinate to a positive value; lowering only the ten shifted
coordinates gives a natural 89 zero. Conversely a natural 89 zero gives a
positive-80 zero via the mixed lift, but its f, r, y coordinates need not be
positive. The proposed reverse map therefore assumes the all-model existential
`PositiveDirectReplacement`: a possibly different zero has all three positive.
The source derives that assumption conditionally from `DirectFY` (f and y
positive at every zero) and `RReplacement` (another zero with positive r,
preserving the original f and y). It does not claim the original r is always
positive. These assumptions, rather than the displayed graph identity, carry
the unresolved model-theoretic content.

The source exposes `SameNoZero` in the 89-to-`positiveShift positive80`
direction and obtains the 89 `PolynomialBridge` only when supplied both the
replacement cut and the bridge for **that exact positive-shifted 80 graph at
the same compact ports**. The final 85 client also requires `ForcedEta K`.
The receipt pins source bytes, including the shifted graph and bridge helper;
it does not establish their imports/providers, any of those premises, an
external coefficient-to-PDF identification, or a complete iPRA endpoint.
The source-level maps and theorem applications remain unelaborated.

From `Computability/DiophantineConsistency`, reproduce the receipt with:

```
python3 -I -S -B reviews/ordinary13-natural89-to-positive80-mixed-shift-independent/check.py
```
