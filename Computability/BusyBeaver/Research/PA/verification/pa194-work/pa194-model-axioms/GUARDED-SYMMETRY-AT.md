# Full-source pointwise translated equality symmetry

`fullSource_pointwise_symmetry` proves the guarded sequent `¬tr(y = z), tr(z = y)` for every pair of model-valued free-variable indices, with no extra source-proof assumptions. It specializes the previously checked closed symmetry twice, using exact arithmetic-syntax quote and substitution equations, then inverts the translated disjunction.

This is a model-level candidate-PRA plus arithmetic-IΣ₁ result. Pointwise transitivity and the resulting `uVar` field still need their proofs; no native iPRA theorem or machine equivalence follows yet.

The checker rebuilds the disjunction-inversion, symmetry-syntax, and final source modules in one fresh output and pins their sources and direct prebuilt repository objects; transitive imports remain prebuilt. Run from the repository root:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-guarded-symmetry-at.sh "$PWD" /dev/shm/pa194-guarded-symmetry-at-replay-NEW
```

All printed axiom reports omit `sorryAx`.
