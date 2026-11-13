# Independent local compact decoder equivalence audit

The read-only [audit](audit.py) of `842f77f47a` actually exited 0 in session
39745; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record the paired source/object/log and seed chains, direct dependencies,
child and outer exits, complete inherited overlay inventory and successful
reruns of the forward-decoder and mask-converse independent audits. Both
reports list `propext`, `Classical.choice`, and `Quot.sound` without warnings
or `sorryAx`. No Lean compile was rerun.

For an external finite index type, model-valued f and v, and model W, put
`n = ∑ f` and `P = ∑ (2^41 − v) f + W`. In every IΣ₁ model, assuming
`n < 2^10`, `W < 2^41`, and `0 < v(i) < 2^41` for each i, the theorem
proves both directions between `NoCarry(n + 2^10 P, 2^51 − 2)` and the
disjunction of an empty cell (`f` and W all zero) or exactly one selector 1
with all others zero and W equal to its value. All powers and subtraction are
model operations. The forward direction uses the conditional decoder; the
reverse reduces the finite sums to the two separately verified mask values.

This local equivalence does not derive its assumptions from the 95-row
graph, bind the external finite index or payload to the actual 943-entry
table, simulate the machine, calibrate the checker, or establish an iPRA
proof. Inherited window providers lack complete printed axiom inventories;
Foundation outer-wrapper and package-transitive/dynamic ancestry
qualifications remain. Resource measurements are samples. Merge `f6ad1e00b1`
added three thirteen-variable sources that were not inputs to this pair.
