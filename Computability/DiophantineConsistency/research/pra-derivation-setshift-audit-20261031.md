# Set-shift witnesses in the derivation core

Foundation's actual `Derivation.blueprint` uses `setShiftGraph` in the
`allIntro` and `shiftRule` branches. In the positive core the former has an
existential output witness, while the latter places the output directly in a
graph. In the negative of the pi core, the negation of the corresponding
universal graph tests produces existential graph witnesses. These cases must
be bounded in arbitrary candidate-PRA models, not merely in the standard model.

`setShiftGraph` says that each member of the output is a shifted member of the
input, and that every member of the input has a shifted image belonging to the
output. The only unbounded existential inside that graph is the image in the
second conjunct. Its membership in the output bounds it by the output itself.
Thus a candidate-PRA `WB` proof for the graph can be assembled from the
existing `WB` proofs for `shiftGraph` and `bitDef`, with that local bound.
The conditional `PRAWitnessSetShiftGraph.wb_setShiftGraph` theorem has
and its `#print axioms` check compiled without warnings against an exploratory
overlay using rebuilt model-pairing, witness-calculus, transfer, and arithmetic
objects. The check reports `propext`, `Classical.choice`, and `Quot.sound`.
It still takes the shift-graph `WB` proof as an explicit hypothesis. The merged
`PRAWitnessFormulaFunctions.wb_shiftGraph` is intended to discharge it, after
that module and its source closure have been built and authenticated.

For the separately quantified *whole output*, the merged
`PRAWitnessCodeGrowth.setShift_le` proves in every model of `IΣ₁` that

    setShift s ≤ 2^(2^(((s + 2)^2 + 13) · s² · 64 + 1)).

This expression can be represented by two nested `BoundTerm.exp2` constructors
with outer multiplier 1. The witness-transfer theorem uses the stronger
`IΣ₁` models only on the source side of the metatheoretic comparison; it does
not assert that arbitrary candidate-PRA models satisfy `IΣ₁`. The required
actual transfer, graph certificate and derivation-core assembly remain to be
checked. In particular this note does not establish the full refutation
witness bound, the HA equivalence, or source-current replay of the upstream
`PRAWitness` dependency graph.

The first exploratory dependency build stopped at `PRAHistoryTruncation`:
the historical `PRAModelIOpenPairing` object did not contain the newer
`standardModelISigmaZero` declaration. A replacement build is underway. The
failed build is not evidence for the newer upstream sources.
