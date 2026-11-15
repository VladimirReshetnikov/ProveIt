# Remaining PAeq fixed axioms after multiplication-zero

This package applies the separately replayed source proof for `mulZero` to reduce the finite fixed-axiom supplier from nine assumptions to eight. The remaining fixed axioms are symmetry, transitivity, successor congruence, addition congruence, multiplication congruence, addition successor, multiplication successor, and successor injectivity. `root_theoryAxiom_of_eight_and_induction` still assumes source proofs for all eight typed axioms and a supplier for arbitrary internally coded induction axioms. It is a model-level source-sequent axiom-field reduction in candidate PRA + IΣ₁ models, not a completed compiler or native iPRA implication.

Reproduce from the repository root with a new empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-forward-fixed-eight.sh "$PWD" /dev/shm/pa194-forward-fixed-eight-repo-NEW
```

The checker rebuilds this reduction and the four-report axiom audit; it uses the separately source-replayed mulZero and fixed-nine outputs and other explicitly listed retained prebuilt overlays. Full dependency-closure replay is not claimed.
