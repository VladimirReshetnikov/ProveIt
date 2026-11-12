# 13/93 q³ quotient: conditional model draft

This packet transcribes the exact 13/95 parent and 13/93 child graphs to inert
Lean literals and four-residual vectors. It proposes an all-model quotient
lemma and conditional same-no-zero transfer. **No source in this packet has
been elaborated by Lean**, and it does not establish an iPRA endpoint.

The quotient lemma works in an arbitrary model `V` with the repository's
ordered-ring structure and IΣ₁-model instance. For natural `b,y,n`, positive
`y`, and signed `z,t,bt` in `DiffRing V`, its graph-facing hypotheses are

```
h = (1+b)*((1+b)*(1+b))
z = h*b*t + y*b - h*bt
z² = (h*b)²*n.
```

It proposes `∃ s : V, 0<s ∧ y=h*s`, with the quotient in the **same model**.
The proof draft uses `ModelRelationCombining.sq_dvd_sq` to obtain signed `h∣z`
from `h²∣z²`; that source theorem uses the model's signed magnitudes and
`ArithmeticSquareDivisibility.dvd_of_square_dvd`. It then gets `h∣y*b`, uses
the explicit ring identity `(1+b)³ - b*(b²+3*b+3) = 1` to cancel `b`, and
uses `Trace75IntegralTransport.natural_dvd_of_signed` to reflect `h∣y` back
to the model naturals. Positivity of `y` gives positivity of `s`. The algebra,
imports, tactics and provider ancestry all require Lean verification.

The conditional transfer supplies parent and child valuations, changing only
coordinate 7. `GraphObligations` explicitly requires the signed norm cut from
a parent zero and both graph zero maps; the source checker does not discharge
these. The external graph checker confirms the intended algebra
`Zparent=h*Zchild`, `A0parent=h²*A0child` and agreement of the other three
residuals, but this is not model-level Lean evidence. The local transfer
requires that signed port zero equal the image of a model-natural beta; the
other three signed ports are arbitrary. `BetaRepresented` leaves that property
explicit in every model.

The native client also takes the parent's `PolynomialBridge` as an explicit
Lean-level hypothesis. This packet does **not** construct that bridge, prove
compact port representation or equality with current-2011 ports, supply an
internal iPRA proof, authenticate compiled providers, or establish inherited
parent calibration and endpoint claims. In particular the 13/95 parent zero
maps and compact44 interpretation remain externally documented qualifications.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-qcube93-model-draft/check.py | cmp - research/ordinary13-qcube93-model-draft/receipt.json
```

This read-only check pins graph and theorem source bytes, checks the two
four-entry vector arities and DAG sum wiring, and reruns the external graph
checker. It does not execute Lean, stage artifacts or verify provider ancestry.
