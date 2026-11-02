# Independent compact empty/copy audit

The read-only [audit](audit.py) of `4fcbaa5145` exited 0 in session 70400;
its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matching source/object/log chains, direct imports, child and outer
exits, and a successful rerun of the window-parent audit. No Lean compile was
rerun. Both axiom reports per side list `propext`, `Classical.choice`, and
`Quot.sound`, without warnings or `sorryAx`.

In an IΣ₁ model, `empty_copy` assumes `W < A` and `A ∣ W`, and concludes
`W = 0`. `selected_copy` assumes `0 < v < A`, `W < A` and
`A ∣ (A − v + W)`, and concludes `W = v`; subtraction is model-natural
subtraction. Neither theorem derives these premises from the graph or binds
the compact payload. The failed exploratory attempts remain in the source
packet; their logs are not successful proof evidence.

The inherited providers lack a complete printed axiom inventory; Foundation
outer-wrapper and package-transitive/dynamic ancestry qualifications remain.
Resource measurements are sampled. This is not checker calibration or an
iPRA proof. Merge `f6ad1e00b1` later added three thirteen-variable sources that
are not inputs to this frozen pair.
