# Guarded addition output-existence source field

The source derivation constructs output existence for the exact ordinal `addResult` relation, under the input domain guards, from fixed equality, empty-set, adjunction and intersection assumptions and one closed Separation instance for the negated addition-prefix property. The first module identifies that instance with the standard universal closure, proves it shift-invariant and reopens it at the needed free variable. The quote module proves its target sentence is exactly `tHyp sA1`. The model wrapper discharges all fixed assumptions into the full adjunctive/separation source theory using the generic typed Separation membership theorem. Thus `PA194AdditionTotalGuardedSource.a1` holds in every candidate PRA model equipped with classical IΣ₁, including nonstandard models.

This is the single `SourceFacts.a1` field, not a complete source interpretation, full multiplication totality, native iPRA theorem, or machine-synchronization result.

From the repository root, with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-source-a1.sh "$PWD" /dev/shm/pa194-source-a1-repo
```

The checker rebuilds all four source modules in one output, rejects `sorryAx`, and checks nine axiom reports. It retains prebuilt dependencies, especially the older `/dev/shm/pa194-addition-output-test`, `/dev/shm/pa194-addition-zero-law-probe`, `/dev/shm/pa194-induction-probe`, the updated naming objects, and Foundation objects. This is an incremental replay, not a source rebuild of the entire addition proof dependency closure.
