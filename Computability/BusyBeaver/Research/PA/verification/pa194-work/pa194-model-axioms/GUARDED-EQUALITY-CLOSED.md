# Guarded closed equality symmetry and transitivity

`fullSource_symmetry_guarded` and `fullSource_transitivity_guarded` supply the translations of the actual closed PAeq equality axioms in the full source theory, using identity packets. They transport existing source-root derivations with packet independence; no additional source-proof hypotheses are introduced.

These are model-level guarded proofs under candidate PRA plus arithmetic IΣ₁. They do not yet provide their pointwise sequent instances, the `uVar` field, or a native iPRA result. The checker rebuilds this module and pins its source and direct imported objects; transitive dependencies remain prebuilt. Run from the repository root:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-guarded-equality-closed.sh "$PWD" /dev/shm/pa194-guarded-equality-closed-repo-NEW-NEW
```

Both printed axiom reports omit `sorryAx`.
