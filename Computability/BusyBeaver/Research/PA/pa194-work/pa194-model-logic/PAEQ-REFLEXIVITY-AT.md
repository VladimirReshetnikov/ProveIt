`atTermCode` is an explicit unary PAeq proof-code constructor. `atTermCode_definable` gives a fixed Σ₁ definition, and `atTermCode_valid` proves that for every internally valid closed PAeq term t in every arithmetic IΣ₁ model, including nonstandard t, its output is a valid ordinaryPAeq proof of t = t. The theorem uses the Δ₁ instance projected from the same internalized theory as the typed proof. The derivation specializes the actual finite PAeq reflexivity axiom using the independently replayed PAeq specialization construction.

This proves reflexivity at a closed term; it does not supply equality congruence for arbitrary formulas, compile PA induction or establish an iPRA consistency implication. The audit rebuilds the new source and six-report top against the repository-source-replayed PAeq specialization and retained dependencies. Foundation and other workspace dependencies are prebuilt, including `/dev/shm` as an object root; this is not a clean whole-workspace build. From the repo root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-reflexivity-at.sh "$PWD" NEW_EMPTY_OUTPUT \
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
