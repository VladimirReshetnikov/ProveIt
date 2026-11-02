# Independent conditional mixed-mask slot audit

The read-only [audit](audit.py) of `3c72abc8a5` actually exited 0 in session
69769; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both source/seed/object/log chains, full inherited overlay inventory,
direct imports, recorded child and outer exits, and a successful rerun of the
independent mixed-bound parent audit. Both reports contain the three expected
theorem names and Lean metatheory `propext`, `Classical.choice`, and
`Quot.sound`, without warnings or `sorryAx`. No Lean compile was rerun.

In an IΣ₁ model, each theorem assumes `NoCarry X M` and an explicit value of
the model radix digit `dig 67 M k`. For masks `2^67−1`, `2^67−2` and
`2^67−4` respectively, the conclusions are `dig 67 X k = 0`, `≤ 1` and
`≤ 3`. Internal powers and digit operations are used. The mask-digit
equalities are hypotheses, not established here for compact44 MC. Global
no-carry is also assumed; the incremented origin, clean reset, full tuple,
machine simulation, checker calibration and iPRA equivalence remain open.

The first independent audit invocation exited 1 before any parent check
because a copied generic audit expected at least 11 committed files; this
packet has exactly nine. The corrected audit checks nine and exited 0.
The inherited provider lacks a complete printed axiom inventory; Foundation
outer-wrapper and package-transitive/dynamic ancestry qualifications remain.
Resource measurements are sampled.
