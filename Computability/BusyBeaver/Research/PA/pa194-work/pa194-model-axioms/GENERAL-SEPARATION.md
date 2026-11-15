# General one-parameter separation

The source snapshot and checker establish, in each model of PRA plus IΣ₁, a definable inverse opening of every internally valid arity-zero source formula. This includes nonstandard codes. Specifically, `bindFormula_scope_open` proves that `bindFormula 0 p` has arity one and opening it at free variable zero gives `p`.

For any internally valid arity-one property `φ`, `sepRoot_scoped` proves the separation instance has arity zero, and `oneBoundSeparation_leaf` proves the translated compiler axiom leaf for `∀ bindFormula 0 (sepRoot φ)`, assuming source sequent well-formedness, membership of this formula, and `SeedAdmission` at that actual axiom node. There is no independent inverse-opening or pushed-admission premise. The result binds only the first free parameter: additional free variables can remain. It is neither general sentence closure nor a native iPRA derivation.

Run from the repository root:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-general-separation.sh "$PWD" \
  /dev/shm/pa194-ranked-open-separation-replay-v3 \
  /dev/shm/pa194-unrestricted-all-replay \
  /dev/shm/pa194-full-one-level-audit \
  /dev/shm/pa194-general-separation-replay
```

The output must not already exist. The eight required source modules and the 14-declaration axiom audit are compiled in one fresh output. The checker pins those sources and two selected imported objects before and after the replay, checks 14 axiom reports, and rejects `sorryAx`. The other overlay dependencies, Foundation, and Mathlib are prebuilt; this is a staged replay, not a from-scratch Foundation build. Successful replay log: `/tmp/pa194-general-separation-replay.log`.
