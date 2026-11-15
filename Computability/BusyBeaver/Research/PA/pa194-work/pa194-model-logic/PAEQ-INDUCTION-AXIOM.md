The source builds a fixed Σ₁ graph for an internal PAeq derivation consisting of a single induction-theory axiom leaf. For every model of arithmetic IΣ₁ and every internally valid arity-one PAeq property p, including nonstandard codes, `closedInductionProof_valid` proves `Proof ordinaryPAeq (closedInductionProof p) (closedInduction p)`. No assumption that the model satisfies PA is used. This is an axiom leaf for the PAeq induction formula, not a proof of the arithmetic-to-PAeq induction supplier. In particular, arithmetic induction uses x + 1 while this formula uses primitive successor; their codes differ, requiring a target congruence proof for arbitrary internal properties. It does not establish the remaining compiler fields, physical synchronization, or an iPRA consistency implication.

The single-output replay rebuilt both source and audit against the previous single-output classifier audit and the retained baselines, with prebuilt Foundation and workspace dependencies; it is not a clean workspace build. The original output `/dev/shm/pa194-paeq-induction-axiom-replay` passed with three clean axiom reports. Reproduce from the repo root with a fresh empty output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-paeq-induction-axiom.sh "$PWD" NEW_EMPTY_OUTPUT \
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
 /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit
```
