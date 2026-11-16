# Internal ordinal-induction base and conclusion syntax

In every model of PRA plus IΣ₁, the fixed parameter-free Σ₁ graphs `inductionBaseGraph` and `inductionConclusionGraph` compute the source codes

```
inductionBaseCode d z p = ∀(¬(d ∧ z) ∨ p)
inductionConclusionCode d p = ∀(¬d ∨ p)
```

from arity-one source formula codes. These operations are total and unique; if their inputs are internally scoped at arity one then their outputs are internally scoped at arity zero, including for nonstandard formula codes. Their domain and zero templates are supplied as input codes: the graph does not contain an evaluated giant constant.

`inductionBaseCode_quote` and `inductionConclusionCode_quote` prove exact equality with the existing typed `Ordinal.inductionBase p` and `Ordinal.inductionConclusion p` when those template inputs are quotes of `domain (#0)` and `zero (#0)`. The typed property p may have arbitrary standard free parameters and nested syntax. These are syntax constructors, not proofs of either formula, a construction for the induction step or full schema, an ordinal PA interpretation, or a native iPRA theorem.

Replay from the repository root, using a fresh final output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-base-conclusion.sh "$PWD" \
  /dev/shm/pa194-typed-schema-replay \
  /dev/shm/pa194-ordinal-base-conclusion-replay
```

Four source modules and a six-declaration axiom audit are rebuilt in a single output. The checker pins the source and two selected imported objects before and after; other staged overlays and Foundation are prebuilt. It rejects `sorryAx`. Successful log: `/tmp/pa194-ordinal-base-conclusion-replay.log`.
