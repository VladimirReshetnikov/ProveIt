# Independent finite-sum compact decoder audit

The read-only [audit](audit.py) of `2ad42e3c7d` actually exited 0 in session
16145; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matching source/object/log chains, direct imports and child and
outer exits. It reruns all three independent decoder-parent audits, checks
each copied seed and the complete joined overlay against the divisibility
branch and shared window provider. Both reports list Lean metatheory
`propext`, `Classical.choice`, and `Quot.sound`, without warnings or
`sorryAx`. No Lean compile was rerun.

For an external finite index type, model-valued selectors f and values v,
and a model natural W, set `n = ∑ f` and `P = ∑ (2^41 − v) f + W`.
The theorem assumes `n < 2^10`, `W < 2^41`, `0 < v(i) < 2^41` for every
index, and `NoCarry(n + 2^10 P, 2^51 − 2)`. It concludes either every
selector and W is zero, or one selector is 1, every other is zero, and W is
that selected value. The powers, subtraction and no-carry predicate are model
operations. The proof does not assume global carry-freeness of the payload
sum, and does not derive these premises from the graph or bind the external
finite index to the actual 943-entry language.

This conditional model theorem is not a full decoder converse, machine
simulation, checker calibration, or iPRA proof. Inherited window providers
lack a complete printed axiom inventory; Foundation outer-wrapper and
package-transitive/dynamic ancestry qualifications remain. Resource numbers
are samples. Merge `f6ad1e00b1` later added three thirteen-variable sources
that were not inputs to this frozen pair.
