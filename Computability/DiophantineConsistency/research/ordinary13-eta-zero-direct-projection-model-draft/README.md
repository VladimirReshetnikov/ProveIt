# Eta-natural direct carrier: conditional power projection

This is an **unelaborated fact-level source draft**. It does not extract a
prototype graph zero, prove eta-zero exclusion, or establish an iPRA endpoint.

The client takes the exact no-`E*q` oriented balance from the prototype, the
same exact-index witness `w`, the same natural quotient `s` in `Y=q³*s`,
and the same natural oriented `main`. With

```
a=X*Y+Y, H=3+4a, U=Y*q², W=4*X*q*s*w,
k=R+1+4*X*Y²*w,
```

it derives `4*X*Y²*w=U*W` and the balance required by the existing
`DirectMainProjection.direct_projection`. The positive `q,s` hypotheses
supply `U>0`. The independent growth assumption `2^R<Y`, combined with
`Y>0`, gives both `X<H` and `2^R<H`. The supplied Pell coordinates must be
`xcoord R (Y*(X+1))=main` and `ycoord R (Y*(X+1))=c` for **the same main**
as the carrier. The existing `projection_quotient` then supplies the required
Pell projection, and the draft concludes `X=2^R`.

No factor-three cancellation, `q∣X`, coprimality or Bézout premise is needed
for this conditional projection. The graph's own `X=q*n_w` and positivity
can later help derive `X≥16` for `power_bound`, but this packet does not
claim that bound or the separate first/main witness reconstruction. The
actual graph zero-to-factor extraction, natural signed-pair orientation,
index congruence, paired indices, first/main recurrence coordinates, rank
bounds, growth, fixed port/model casts, provider closure, Lean axiom reports,
eta-zero contradiction, and graph-zero maps all remain open.

Run `python3 -I -S -B research/ordinary13-eta-zero-direct-projection-model-draft/check.py`
from `Computability/DiophantineConsistency`, and compare with `receipt.json`.
The deterministic checker checks source interfaces and bounded arithmetic
identities; it does not run Lean or prove a model-level statement.
