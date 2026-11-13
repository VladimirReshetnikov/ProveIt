# Independent mixed low-mask bounds audit

The read-only [audit](audit.py) of `4b4428b33a` actually exited 0 in session
62259; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matched source/object/log chains, direct imports, recorded child
and outer exits, and a successful rerun of the window-parent audit. The
three named reports per side list Lean metatheory `propext`,
`Classical.choice`, and `Quot.sound`, without warnings or `sorryAx`. No Lean
compile was rerun.

For an IΣ₁ model and a model element x, each theorem assumes explicitly
`x < 2^67` and its respective internal no-carry condition. Against masks
`2^67−1`, `2^67−2` and `2^67−4`, the respective conclusions are `x = 0`,
`x ≤ 1` and `x ≤ 3`. The dummy case permits all four values; the proof
peels two low bits and bounds the remaining model-natural quotient. These
are local conditional facts, not proofs of the actual MC model digits,
graph-derived no-carry, a global carry bound or clean reset.

The retained first exploratory attempt failed and contained `sorryAx`; it is
not proof evidence. Inherited window providers lack complete printed axiom
inventories, and Foundation outer-wrapper and package-transitive/dynamic
ancestry qualifications remain. Resource measurements are samples. The theorem
does not establish machine simulation, checker calibration or iPRA equivalence.
