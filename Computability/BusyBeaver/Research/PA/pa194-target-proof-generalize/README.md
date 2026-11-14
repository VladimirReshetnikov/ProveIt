# Concrete target generalization closure

`PA194TargetGeneralize.lean` proves `generalize_closed`: in every
candidate-PRA model whose arithmetic reduct satisfies IΣ₁, the concrete
`TargetProvable` relation is closed under the numerical target calculus's
universal generalization rule. This includes nonstandard formulas and proof
vectors. The witness appends a generalization line with Foundation's `concat`;
`prefix_history` proves by internal IΣ₁ induction that the original proof's
history is preserved by that append.

The construction supplies an all-model proof witness, but this package does
not yet provide a fixed finite candidate-PRA code for the proof transformation.
Modus-ponens closure of `TargetProvable`, correspondence to the upstream
certificate encoding, source-proof compilation, and machine/calculus
calibration remain open. This theorem alone does not prove a PA194/Con(PA)
implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-proof-generalize/check.sh
```

The final module was rebuilt against the freshly rebuilt target-proof leaf
module and previously checked history suffix. A full nested replay of this
wrapper has not yet been completed. Its printed axiom dependencies contain no
`sorryAx`.
