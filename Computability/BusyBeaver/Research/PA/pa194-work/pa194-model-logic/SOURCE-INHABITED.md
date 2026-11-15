# Source-theory domain inhabitation

`PA194SourceInhabited.inhabited_provable` proves the exact `Interpretation.inhabited` obligation: in every candidate PRA model satisfying IΣ₁, the full relational source theory proves `∃x. domain(x)`. The construction quotes and discharges the repository's `emptyFoundationDerivation` from the existing full-source empty-set proof, then identifies the quoted formula with the exact `^∃ (domainCode (^#0))` code used by the guarded compiler.

This supplies only the inhabited-domain field. It does not supply the arbitrary induction axiom, function-term witness rule, complete interpretation, physical synchronization, or an iPRA implication.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-source-inhabited.sh "$PWD" /dev/shm/pa194-source-inhabited-repo-NEW
```

The checker rebuilds `PA194FoundationOrdinalInhabited` directly from the current repository source, then this source module and a three-report axiom audit. Other imports use explicitly enumerated prebuilt paths; it does not rebuild the full dependency closure.
