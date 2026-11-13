# Outer data from an actual positive 2011 carrier zero

[`Model69CurrentOuter.lean`](Model69CurrentOuter.lean) proves in every `IΣ₁`
model that the exact maintained 2011 14-coordinate expression supplies the
outer data below. Its hypotheses are **only** positivity of all fourteen
model-natural coordinates `v` and equality of the two split-natural sides of
`ObjectCurrentEquation2011.expression` at `v`. The expression uses the full
fixed `CurrentWindowCarry2011.ports` tuple; this is not the distinct
phase-split2471 or compact44 tuple.

Write `q=ArithmeticCarrierRadix2011.q v`,
`R=ArithmeticCarrierRadix2011.rank v`, `C=q-v₁-v₂`,
`X=ArithmeticCarrierRadix2011.X v`, and
`Y=ArithmeticCarrierRadix2011.Y v`. The theorem constructs model naturals
`L,G` such that

```
L>0, R>0, C>0, G>0,
CurrentMasks2011.beta*v₀ ∣ G,
(CurrentKernel2011.K+v₈)*C = v₁+G,
(v₁₀+v₁₁)*Y+v₁₀ = ycoord R (X*Y+Y).
```

The proof applies the existing actual-zero equation, power and population
bounds, the model population upper bound, the independently audited scalar
outer composition, and the maintained first/main index theorem. The original
parent zero supplies its own strong and auxiliary norms, which are used to
recover the parent ordinate; no new thirteen-coordinate witness is assumed.

This is an **actual-zero model theorem**, not the 13-variable converse or an
object-level iPRA derivation. In particular, this packet does not prove
`R%4=3`, identify the displayed natural values with every signed
`Carrier65.core` field, construct the 13-coordinate zero, or bind an exact
69-row literal at 2011 ports. No theorem for the phase-split2471 tuple follows.

## Paired replay

[`replay.py`](replay.py) checks and reruns the independently audited
[20-module prefix](../../reviews/thirteen-model-parent-prefix-pair-independent-audit/README.md)
and [conditional scalar outer](../../reviews/thirteen-model-parent-outer-independent-audit/README.md)
parent audits before and after compiling this caller against each
corresponding parent side. It pins source, compiler and audit inputs, checks
direct imports, uses `-M4000 -j1`, and records observed child exits and hashes.
Session 24583 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_CURRENT_OUTER 4fdcf2e09603016712d10a8f22f50de58d0c32ac8d87b4867910a01b73ef0d8c`.
The [receipt](replay-receipt.json) and [terminal observation](terminal-observation.json)
record successful corresponding builds, matching objects and the actual
outer exit. The theorem reports `[propext, Classical.choice, Quot.sound]`
with no warnings or `sorryAx`. These are Lean metatheory dependencies, not
axioms asserted for object-level iPRA.

This paired suffix has not yet received a separate independent audit. The
20-module prefix audit checked its artifacts and direct guards but did not
produce a complete axiom inventory for those modules. Package-transitive and
dynamic ancestry and the original Foundation wrapper's unobserved exit
remain inherited. The initial exploratory caller session 5837 also actually
exited 0; it is superseded by the paired run above.
