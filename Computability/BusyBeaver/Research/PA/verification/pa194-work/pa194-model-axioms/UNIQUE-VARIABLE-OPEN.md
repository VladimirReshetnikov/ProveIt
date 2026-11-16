# Variable uniqueness reduced to pointwise equality cancellation

`uniqueVariable_opened_exact` computes the two eigenvariable openings in the generic `uVar` reduction. `guarded_uVar_of_equality_cancellation` derives the entire variable-uniqueness field from guarded translations of the three-formula equality-cancellation sequent for every model-valued index. The cancellation sequent remains an explicit assumption: this is not an unconditional `uVar` proof.

The theorem is model-generic for arithmetic IΣ₁ and a Δ₁ source theory; it is not a native iPRA theorem. This script rebuilds the module in a fresh output and checks the source and direct imported object pins. Transitive dependencies are prebuilt. Run from the repository root:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-unique-variable-open.sh "$PWD" /dev/shm/pa194-unique-variable-open-repo-NEW-NEW
```

All six printed axiom reports omit `sorryAx`.
