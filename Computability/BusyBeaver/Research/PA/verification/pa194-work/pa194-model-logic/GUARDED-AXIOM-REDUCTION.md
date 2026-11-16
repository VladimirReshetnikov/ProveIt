# Ordinary axiom supplier reduced to five cases and induction

`packet_axiom_supplier_of_five_and_induction` proves source provability of the exact translation of every internally valid ordinaryPAeq axiom under any valid arity-zero packet, conditional on source proofs for the five remaining fixed axioms and for each arbitrary internally coded closed induction axiom. The proof uses the finite axiom classifier and the separately replayed ordinary-axiom packet bridge; it does not assume the problematic unguarded `RemainingRules` invariant.

This result provides the source-provability premise needed by the guarded compiler's axiom field. The five fixed cases, arbitrary induction supplier, function-term witness rule, inhabited domain, full compiler, physical synchronization, and native iPRA implication remain separate obligations. The theorem holds in every candidate PRA + IΣ₁ model, including nonstandard models.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-guarded-axiom-reduction.sh "$PWD" /dev/shm/pa194-guarded-axiom-reduction-repo-NEW
```

The checker rebuilds one source module and a one-report audit, using the separately replayed five-case reduction, repository-replayed packet bridge, and other explicitly listed prebuilt paths. It does not rebuild the full dependency closure.
