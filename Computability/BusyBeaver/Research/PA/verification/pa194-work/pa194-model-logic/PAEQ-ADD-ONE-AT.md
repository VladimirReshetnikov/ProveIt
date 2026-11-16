`paeqSpecializeProof` constructs a target-calculus derivation of p[t] under a shared arbitrary internal sequent from a derivation of ∀p under that context. It applies to all model-valued well-scoped p, closed terms t, sequents and derivation codes, including nonstandard values. `paeqSpecializeCode` is the explicit proof-code constructor, and `paeqSpecializeGraph_defined` establishes its fixed Σ₁ graph. This is a PAeq-language adaptation of the previously formalized source-language specialization construction, not a new general proof compiler.

`addOneAt` combines that construction with the source-replayed fixed add-one proof and its model-uniform quotation. In every arithmetic IΣ₁ model it constructs a typed ordinaryPAeq proof of the add-one property specialized to an arbitrary internally valid closed PAeq term, including nonstandard term codes. `addOneAtCode_valid` additionally gives the explicit raw proof code and formula, using the Δ₁ instance projected from the same internalized theory. It does not yet prove formula congruence under such an equality or supply arithmetic induction, and does not establish an iPRA consistency implication.

The independent replay builds both source modules and the seven-report top against the repository-source-replayed internal proof and retained source/overlay baselines; Foundation and workspace dependencies are prebuilt, including `/dev/shm` as an object root. It is not a clean workspace build. Reproduce from the repo root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-add-one-at.sh "$PWD" NEW_EMPTY_OUTPUT \
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
