# Residue-90 X=0 model arithmetic draft

This source-only packet proposes the main-norm obstruction needed to force X
positive. It does **not** extract its hypotheses from the residue graph, and
none of the Lean source, tactics, imported providers or axiom checks has
been elaborated.

The fact-level theorem `modulus_dvd_scale` works in the difference ring of an
ordered IΣ₁ model. It assumes `U≠0`, a signed root shape
`z=U*(a*c)+H*t`, and the squared norm
`z²=U²*(1+(H+a²)*c²)`. Signed square divisibility yields `z=U*d` for a
signed model-ring `d`; cancellation yields

```
H ∣ U*(d-a*c),       (d-a*c)*(d+a*c)=1+H*c².
```

The separate `cancel_modulus` proof uses the explicit displayed product to
show `H∣U`, without a coprimality axiom or an assumption on the sign of `d`.
The `xzero_impossible` client takes `q≥2`, `Y≥q³`, the X=0 specializations
`H=3+4Y`, `U=Y*q²`, and the exact signed main shape and norm. It obtains
`H∣3q²`, reflects that divisibility to model naturals with
`Trace75IntegralTransport.natural_dvd_of_signed`, and contradicts
`3q²<H` because `Y≥q³≥q²`.

The literal graph must still provide these signed identities, `q≥2`, and
`Y≥q³`; its beta/K0 representations, J positivity, source graph/provider
link and compact fixed-kernel endpoint are separate. This packet proves no
Lean-checked graph zero map or internal iPRA equivalence.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-xzero-model-draft/check.py | cmp - research/ordinary13-residue90-xzero-model-draft/receipt.json
```

The read-only checker pins source/theorem bytes, checks the explicit ring
certificate on bounded integer instances and separately controls the size
inequality. It does not run Lean, stage files or authenticate providers.
