# Natural order for the auxiliary Pell ordinate

`CompactAuxOrdinateOrder.ordinate_ge` proves in every model of `IΣ₁` that
`w≤y` whenever `I>0`, `y>0`, and

```
I*I*w*w + y*y = 1 + I*I*y*y.
```

It is a generic model-natural result, including nonstandard model elements.
The auxiliary seed has precisely this norm with `I=delta a*i*c*c`; its
separate positivity facts can be used to establish the lemma's explicit
hypotheses. The inequality lets a downstream client identify the natural
subtraction `y-w` with the difference in the model difference ring. It is
needed for the exact ordinary graph coordinate `delta a*i+(y-w)` when the
graph's `V` is the auxiliary seed's `w`. This theorem does not itself supply
those seed hypotheses, any graph-evaluation binding, an exact graph zero or
an iPRA proof.

The single-author bounded `observations/attempt04` exited 0 without warnings
or `sorryAx`. The named Lean metatheory axiom report is exactly
`[propext, Classical.choice, Quot.sound]`, not an object-theory axiom list.
Source SHA-256:
`89ef868199f19ab6fc5d72d8ff00cafd587b2dd6fc4b0087410ac4f9737721d7`;
object SHA-256:
`b0c61170406b3a47465f3413f1a11313d07bac9b09f4b56781ac6701cbb98679`.
Exact sources, logs, compiler/guard receipts and selected project/root
inventories are retained under the attempt. The earlier attempts record
local tactic/ordering/namespace failures; no failed proof is used here.

The 531 selected seed/halt project overlaps matched at preflight, and the
recorded guards and inventories were unchanged at final checks. This is a
single-author exploratory build, not a paired replay or a complete
authentication of transitive, package or dynamic ancestry. The filesystem
checks are point-in-time, not continuous monitoring.
