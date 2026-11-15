In every candidate PRA model whose arithmetic reduct satisfies IΣ₁, `all_qf_replace` and `exs_qf_replace` prove modeled ordinaryPAeq provability of `(∀p)[a] → (∀p)[b]` and `(∃p)[a] → (∃p)[b]` from modeled provability of a = b, when p is an internally valid arity-two PAeq formula, a and b are internally valid closed PAeq terms, and the opened body `free1 language p` satisfies the existing `InternalQuantifierFree` predicate. All input and proof codes may be nonstandard. The construction shifts the equality proof, proves the explicit opening/substitution identity, invokes the prior nonstandard quantifier-free replacement induction for the opened body, then applies the internal quantified-implication rules.

The quantifier-free condition on `free1 p` is an explicit unproved-for-general-p hypothesis; these are proof-existence theorems, not fixed proof-code functions. They do not cover arbitrary nested quantified formulas, establish the PA-induction supplier, synchronize the physical machine or prove an iPRA implication. The audit rebuilds both source modules and a five-report top against the repository-source-replayed QF formula theorem and retained descendant/other dependencies. Foundation and workspace dependencies are prebuilt, including `/dev/shm` as an object root; this is not a clean whole-workspace build. From the repo root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-one-binder-congruence.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-paeq-qf-congruence-repo \
 /dev/shm/pa194-paeq-logical-congruence-repo /dev/shm/pa194-paeq-negative-atomic-repo \
 /dev/shm/pa194-paeq-atomic-congruence-repo \
 /dev/shm/pa194-paeq-term-congruence-repo /dev/shm/pa194-paeq-symmetry-lift-repo /dev/shm/pa194-paeq-transitivity-lift-repo \
 /dev/shm/pa194-paeq-add-congruence-lift-repo /dev/shm/pa194-paeq-mul-congruence-lift-repo /dev/shm/pa194-paeq-succ-lift-repo /dev/shm/pa194-paeq-reflexivity-exact-repo \
 /dev/shm/pa194-paeq-quad-specialization-repo \
 /dev/shm/pa194-paeq-triple-specialization-repo \
 /dev/shm/pa194-paeq-succ-congruence-at-repo \
 /dev/shm/pa194-paeq-reflexivity-exact-repo \
 /dev/shm/pa194-paeq-reflexivity-at-repo /dev/shm/pa194-paeq-arithmetic-induction-repo \
 /dev/shm/pa194-paeq-add-one-at-repo \
 /dev/shm/pa194-paeq-add-one-internal-repo \
 /dev/shm/pa194-paeq-add-one-proof-repo \
 /dev/shm/pa194-paeq-successor-mismatch-repo \
 /dev/shm/pa194-paeq-ordinary-class-repo \
 /dev/shm/pa194-paeq-induction-code-repo /dev/shm/pa194-paeq-typed-closure-repo \
 /dev/shm/pa194-paeq-free-closure-repo \
 /dev/shm/pa194-paeq-closure-repo \
 /dev/shm/pa194-paeq-bind-term-repo /dev/shm/pa194-forward-term-correct-repo \
 /dev/shm/pa194-formula-dispatcher-repo /dev/shm/pa194-term-scope-repo \
 /dev/shm/pa194-term-dispatcher-repo \
 /dev/shm/pa194-paeq-term-formula-tree-repo \
 /dev/shm/pa194-term-formula-paeq-baseline \
 /dev/shm/pa194-multiplication-code-repo /dev/shm/pa194-addition-code-repo \
 /dev/shm/pa194-paeq-template-compose-repo /dev/shm/pa194-paeq-ordinal-params-replay /dev/shm/pa194-paeq-ordinal-values-replay \
 /dev/shm/pa194-source-template-replay /dev/shm/pa194-uniform-fully-closed-replay \
 /dev/shm/pa194-uniform-closure-replay /dev/shm/pa194-fully-closed-replay \
 /dev/shm/pa194-model-separation-full-replay /dev/shm/pa194-model-separation-seeded-replay \
 /dev/shm/pa194-model-closure-definability-replay /dev/shm/pa194-model-closure-replay \
 /dev/shm/pa194-general-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 \
 /dev/shm/pa194-closed-sep-theory-replay /dev/shm/pa194-uniform-sep-combined-replay \
 /dev/shm/pa194-standard-no-free-replay /dev/shm/pa194-closed-sep-classifier-replay \
 /dev/shm/pa194-generic-sim-replay /dev/shm/pa194-adjunctive-sim-v2-replay \
 /dev/shm/pa194-shift-interface-replay /dev/shm/pa194-unrestricted-existential-v2-replay \
 /dev/shm/pa194-qf-ranked-existential-audit /dev/shm/pa194-adjunctive-admission-audit \
 /dev/shm/pa194-general-shift-replay /dev/shm/pa194-general-reverse-shift-replay \
 /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-general-freshness-audit \
 /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit /dev/shm
```
