# Independent compact low-mask converse audit

The read-only [audit](audit.py) of `72040220e5` actually exited 0 in session
21134; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record matched source/object/log chains, direct imports, child and outer exits,
and a successful rerun of the window-parent audit. The two printed axiom
reports per side list Lean metatheory `propext`, `Classical.choice`, and
`Quot.sound` without warnings or `sorryAx`. No Lean compile was rerun.

The two theorems prove in every IΣ₁ model, using internal exponential and
no-carry, that `NoCarry(0, 2^51 − 2)` and
`NoCarry(1 + 2^51, 2^51 − 2)`. The second proof handles model bit
positions on both sides of the 51-bit boundary. They do not establish that
an actual selector sum has either prescribed value, bind the 943-row table,
prove an all-model machine simulation, calibrate a checker, or produce an
iPRA proof.

The source packet retains a failed exploratory attempt with `sorryAx` and a
subsequent warning-bearing attempt, distinct from its successful paired run.
The inherited providers lack a complete printed axiom inventory; Foundation
outer-wrapper and package-transitive/dynamic ancestry qualifications remain.
Resource measurements are sampled. Merge `f6ad1e00b1` added three
thirteen-variable sources that were not inputs to this pair.
