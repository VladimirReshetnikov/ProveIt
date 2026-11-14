# Numerical target line-history bridge

`PA194TargetLineSoundness.lean` proves `line_sound` in every candidate-PRA
model whose arithmetic reduct satisfies IΣ₁. Given an internal Foundation
vector of numerical formulas, it assumes each line is one of the nine target
seed forms, an MP conclusion with two earlier lines, or a universal
conclusion with an earlier line. The explicit `Seed` definition includes the
rho8 inequality and both oldBundle freshness guards. Under exactly those
line-condition hypotheses, every line is `TargetProvable` in the independent
target proof encoding, including at nonstandard model indices.

The proof discharges all seed, MP and generalization preservation cases using
the concrete target relation and uses internal IΣ₁ induction over line
indices. Its proof witnesses include the model-level Σ₁ Skolem construction
used for MP; it does not supply a fixed finite proof-transformer code.

The theorem does **not** show that an actual PA194 controller or scheduler
execution supplies a vector satisfying the line condition. Nor does it
identify `TargetProvable` with Foundation PA provability or with the upstream
certificate format. Those bridges and machine/calculus calibration remain
open, so this is not yet a PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-line-sound/check.sh
```

The final module was rebuilt against the freshly checked MP-closure module
and previously checked history suffix. A full nested replay of this wrapper
has not yet been completed. Its printed axiom dependencies contain no
`sorryAx`.
