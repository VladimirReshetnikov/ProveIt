# Candidate-PRA codes for PA194 vector and atomic formula shift

`vectorShiftCode` is a fixed finite candidate-PRA code, composed from the
certified term-shift code and the previously certified pair projections.
`vectorShift_complete` proves its interpretation equals Foundation's
`termShiftVec language 2` on **every internally valid two-term vector** in
every candidate-PRA model whose arithmetic reduct satisfies IΣ₁. This includes
nonstandard vectors and nonstandard term codes.

`atomShiftCode` is a fixed finite candidate-PRA code built from vector shift,
pairing and the same certified projections. The all-model
`positiveAtom_model_all` and `negativeAtom_model_all` theorems show that it
agrees with Foundation formula shift on every internally valid positive or
negative source atom. `sourceRelation_arity` proves that every relation
recognized for the PA194 source language has arity two, so these cases cover
all internally recognized source atoms. `positiveAtom_graph` and
`negativeAtom_graph` give the corresponding equations for the actual fixed
parameter-free Σ₁ graph of that same code.

The source modules checked in dependency order against the ordered source and
term-graph overlays. Their printed theorems report
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`. The full nested
standalone replay of this two-chain package remains pending.

The projection codes are once-chosen existential witnesses; their complete
constructor trees are not printed. The results require the internal source
relation and term-vector validity hypotheses. Compound formula shift, a
uniform nonstandard proof compiler, and PA194 machine calibration remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited current
Foundation object overlay and `IPRA_LEAN_OVERLAY` to the pinned audited
project object overlay, then run
`bash Computability/BusyBeaver/Research/PA/pa194-source-atom-shift-code-model/check.sh`.
