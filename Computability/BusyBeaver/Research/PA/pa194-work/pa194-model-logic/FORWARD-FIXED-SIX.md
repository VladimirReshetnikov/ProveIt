# Remaining PAeq fixed axioms after transitivity

This package applies the source proof for fixed PAeq transitivity to reduce the fixed-axiom supplier from seven assumptions to six. The remaining fixed axioms are successor congruence, addition congruence, multiplication congruence, addition successor, multiplication successor, and successor injectivity. `root_theoryAxiom_of_six_and_induction` still assumes source proofs for those six typed axioms and a supplier for arbitrary internally coded induction axioms. It is a model-level reduction of an axiom-supplier obligation, not a completed guarded compiler or native iPRA implication; the separate sentence-packet theorem transfers the resulting axiom proofs to valid identity packets.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-forward-fixed-six.sh "$PWD" /dev/shm/pa194-forward-fixed-six-repo-NEW
```

The checker rebuilds the reduction and four-report axiom audit, using the separately replayed fixed-seven and transitivity results, repository-replayed composition objects, and other explicitly listed retained prebuilt overlays. The full import closure is not rebuilt.
