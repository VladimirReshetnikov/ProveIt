# Guarded interpretation axiom field, reduced to five cases and induction

`interpretation_axioms_of_five_and_induction` proves the exact `Interpretation.axioms` field for ordinaryPAeq and the full relational source theory in every candidate PRA + IΣ₁ model. It uses the packet-independent source-axiom supplier at the compiler's `idParam (p+1)` and promotes the source proof to a guarded derivation with guard bound zero.

Its explicit remaining assumptions are source proofs for the five fixed axioms listed by the separately replayed fixed-five reduction, and a source proof of the translated closed induction axiom for every internally valid arity-one property, including nonstandard codes. It does not assume an unguarded derivation invariant. The function-term witness field, arbitrary induction supplier, full interpretation, physical synchronization and native iPRA implication remain separate; the inhabited field has its own source proof.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-interpretation-axioms.sh "$PWD" /dev/shm/pa194-interpretation-axioms-repo-NEW
```

The checker rebuilds one source module and a one-report audit against the repository-replayed updated guarded calculus, the separately replayed packet axiom reduction, and the explicitly listed prebuilt paths. It does not rebuild the full dependency closure.
