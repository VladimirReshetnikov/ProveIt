# Remaining PAeq fixed axioms after symmetry

This package applies the source proof for fixed PAeq symmetry to reduce the fixed-axiom supplier from eight assumptions to seven. The remaining fixed axioms are transitivity, successor congruence, addition congruence, multiplication congruence, addition successor, multiplication successor, and successor injectivity. `root_theoryAxiom_of_seven_and_induction` still assumes source proofs for those seven typed axioms and a supplier for arbitrary internally coded induction axioms. It is a model-level source-sequent axiom-field reduction in candidate PRA + IΣ₁ models, not a completed compiler or native iPRA implication.

Reproduce from the repository root with a new empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-forward-fixed-seven.sh "$PWD" /dev/shm/pa194-forward-fixed-seven-repo-NEW
```

The checker rebuilds the reduction and four-report axiom audit, using the separately replayed fixed-eight and symmetry results and other explicitly listed retained prebuilt overlays. Full dependency-closure replay is not claimed.
