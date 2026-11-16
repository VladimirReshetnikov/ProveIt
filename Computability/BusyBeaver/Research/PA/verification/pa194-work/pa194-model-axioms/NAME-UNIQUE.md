# Guarded universal introduction and variable uniqueness reduction

`guarded_tr_all_intro` derives the guarded translation of an arithmetic universal from the guarded translation of its eigenvariable opening. `guarded_tr_double_all_intro` handles two universals, with `openedDoubleBody` defined by the exact code-level shift and substitution. `guarded_uVar_of_open` specializes this construction to the uniqueness formula of an arbitrary model-valued free-variable index.

The last theorem **assumes** guarded proofs of the twice-opened translated uniqueness matrix for all indices. It does not discharge `NameFacts.uVar`, nor does it assert a native iPRA theorem. All results are generic over arithmetic IΣ₁ models and a Δ₁ source theory.

The script rebuilds this source in one output and pins its direct source and imported object dependencies. Transitive imports remain prebuilt. From the repository root run:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-name-unique.sh "$PWD" /dev/shm/pa194-name-unique-replay-NEW
```

All seven printed axiom reports exclude `sorryAx`.
