# Binary source-atom inverse to opening

`bindTerm_scoped` proves the previously defined inverse-opening term operation maps a term scoped at depth k to a term scoped at k+1. `bindPair` applies the operation to both slots of a binary source vector, and `bindPair_definable` proves that this model function is Σ₁-definable. `opening_bind_positiveAtom` and `opening_bind_negativeAtom` show that the existing qVec-based opening after this transformation returns the original positive or negative binary relation atom, for arbitrary model-valued k and internally scoped terms. The underlying model satisfies PRA and IΣ₁; nonstandard depths and syntax are included. The four axiom reports list `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

This covers binary atoms and vectors only. It does not yet construct an inverse for arbitrary source formulas or a parameterized separation scheme, and does not establish a PA interpretation or native iPRA/consistency result.

A fresh independent suffix replay exited 0 in `/tmp/pa194-bind-source-atom-replay.log`, using the separately source-replayed term and opening baselines. The checker pins the source and two direct prerequisite objects before and after compiling; other source outputs and workspace/foundational objects remain prebuilt, and their full transitive source closure is not authenticated by these selected pins. This is not a clean whole-workspace build.

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-bind-source-atom.sh "$PWD" /dev/shm/pa194-bind-source-term-replay /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-bind-source-atom-replay
```
