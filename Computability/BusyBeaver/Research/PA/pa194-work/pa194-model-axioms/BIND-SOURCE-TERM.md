# Definable term inverse to opening

In every PRA model whose arithmetic reduct satisfies IΣ₁, `bindTerm k t` replaces free variable 0 by bound variable k, decrements every other free index, and preserves existing bound variables. `bindTerm_definable` gives a Σ₁ definition of this model function by a disjoint-case graph. `opening_bindTerm` proves that the existing qVec-based opening at depth k applied to `bindTerm k t` returns t, for any internally coded source term scoped at k. Depths and term indices may be nonstandard. Both printed reports contain only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

This is the term layer only; it does not construct an inverse on arbitrary formulas, a general parameterized-separation axiom supplier, a PA interpretation, a native iPRA proof, or a consistency equivalence. It includes no function-symbol cases because the relational source language has no function symbols.

A fresh independent source-suffix replay exited 0 in `/tmp/pa194-bind-source-term-replay.log`. It recompiles the new source against a separately replayed source-opening baseline, pins the source and two direct baseline objects before and after, and retains the other source baselines and general workspace/foundation objects prebuilt; their complete transitive source closure is not independently authenticated by the selected pins. It is not a clean whole-workspace rebuild.

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-bind-source-term.sh "$PWD" /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-bind-source-term-replay
```
