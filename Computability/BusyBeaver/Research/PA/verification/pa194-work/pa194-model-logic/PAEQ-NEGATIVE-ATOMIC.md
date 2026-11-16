In every arithmetic IΣ₁ model, for internally valid closed PAeq term codes a and b, and internally valid arity-one term codes s and t, `negative_atomic_replace` proves that modeled ordinaryPAeq provability of a = b entails modeled provability of `(s[a] ≠ t[a]) → (s[b] ≠ t[b])`. It includes nonstandard term and proof codes, using the ordinaryPAeq Δ₁ instance. The proof applies the separately source-replayed positive equality-atom replacement in the reverse direction, symmetry of equality, and classical contraposition internal to the PAeq calculus.

This proves the negative equality-atom case as existence of a modeled proof; it is not a fixed proof-code transformer and does not establish Boolean or quantified formula congruence, the PA-induction supplier or an iPRA implication. The audit rebuilds the new module and one-report top against the repository-source-replayed positive atomic theorem and retained dependencies. Foundation and workspace dependencies are prebuilt, including `/dev/shm` as an object root; it is not a clean whole-workspace build. From the repo root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-negative-atomic.sh "$PWD" NEW_EMPTY_OUTPUT \
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
