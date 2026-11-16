`fixed_provable_to_ordinary` uses the modeled Δ₁-class inclusion and Foundation `Derivation.of_ss` to transport any internal proof from targetFixedTheory to ordinaryPAeq with the same proof code, in every arithmetic IΣ₁ model (including nonstandard proofs). The six named corollaries discharge source arithmetic equality reflexivity, symmetry and transitivity; congruence of the zero and one function symbols; and the PeanoMinus axiom zeroLtOne. Each proves the actual `formulaCode 0` translation in ordinaryPAeq. No PA-model assumption is used.

These six do not discharge the full finite supplier: equality congruence for addition and multiplication, and relation congruence for both equality and less-than, remain, as do the other sixteen arithmetic/order PeanoMinus cases. In particular the repository's `PA194PAeqAddCongruence.lean` is an unfinished draft containing `sorry` and is not imported. The results are modeled proof-existence statements; no iPRA theorem or physical-machine claim is made.

The audit rebuilds twelve existing quote/witness modules directly from their repository locations, the new transfer module, and seven-report audit, against repository-replayed ordinary-theory and ND baselines plus retained Foundation/workspace objects. It is not a clean whole-workspace build. From the repository root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-finite-transferred.sh "$PWD" /dev/shm/pa194-paeq-finite-transferred-repo \
 /dev/shm/pa194-paeq-add-one-proof-repo /dev/shm/pa194-paeq-ordinary-class-repo /dev/shm/pa194-paeq-induction-closure-reduction-repo /dev/shm/pa194-paeq-induction-body-supplier-repo /dev/shm/pa194-paeq-induction-reduction-repo /dev/shm/pa194-paeq-induction-image-repo /dev/shm/pa194-paeq-induction-add-one-repo /dev/shm/pa194-paeq-induction-axiom-repo /dev/shm/pa194-paeq-universal-formula-repo /dev/shm/pa194-paeq-arithmetic-induction-repo /dev/shm/pa194-paeq-add-one-at-repo \
 /dev/shm/pa194-paeq-universal-atomic-repo \
 /dev/shm/pa194-paeq-universal-term-congruence-repo /dev/shm/pa194-paeq-atomic-congruence-repo /dev/shm/pa194-paeq-symmetry-lift-repo /dev/shm/pa194-paeq-transitivity-lift-repo \
 /dev/shm/pa194-paeq-term-congruence-repo /dev/shm/pa194-paeq-add-congruence-lift-repo /dev/shm/pa194-paeq-mul-congruence-lift-repo /dev/shm/pa194-paeq-succ-lift-repo \
 /dev/shm/pa194-paeq-add-congruence-lift-repo /dev/shm/pa194-paeq-mul-congruence-lift-repo /dev/shm/pa194-paeq-succ-lift-repo /dev/shm/pa194-paeq-reflexivity-exact-repo \
 /dev/shm/pa194-paeq-quad-specialization-replay \
 /dev/shm/pa194-paeq-triple-specialization-repo /dev/shm/pa194-paeq-triple-specialization-replay \
 /dev/shm/pa194-paeq-succ-congruence-at-repo \
 /dev/shm/pa194-paeq-succ-congruence-at-replay /dev/shm/pa194-paeq-reflexivity-exact-repo /dev/shm/pa194-paeq-reflexivity-exact-replay \
 /dev/shm/pa194-paeq-reflexivity-at-repo /dev/shm/pa194-paeq-reflexivity-at-replay /dev/shm/pa194-paeq-arithmetic-induction-replay \
 /dev/shm/pa194-paeq-add-one-at-repo /dev/shm/pa194-paeq-add-one-at-replay-v2 \
 /dev/shm/pa194-paeq-add-one-at-replay-v2 \
 /dev/shm/pa194-paeq-add-one-internal-repo /dev/shm/pa194-paeq-add-one-internal-replay \
 /dev/shm/pa194-paeq-add-one-proof-repo /dev/shm/pa194-paeq-add-one-proof-replay \
 /dev/shm/pa194-paeq-successor-mismatch-replay \
 /dev/shm/pa194-paeq-ordinary-class-replay \
 /dev/shm/pa194-paeq-induction-code-repo /dev/shm/pa194-paeq-typed-closure-repo \
 /dev/shm/pa194-paeq-free-closure-repo \
 /dev/shm/pa194-paeq-closure-repo \
 /dev/shm/pa194-paeq-bind-term-repo /dev/shm/pa194-forward-term-correct-repo \
 /dev/shm/pa194-formula-dispatcher-repo /dev/shm/pa194-term-scope-replay \
 /dev/shm/pa194-term-dispatcher-repo \
 /dev/shm/pa194-paeq-term-formula-tree-replay \
 /dev/shm/pa194-term-formula-paeq-baseline \
 /dev/shm/pa194-multiplication-code-replay /dev/shm/pa194-addition-code-replay \
 /dev/shm/pa194-paeq-template-compose-replay /dev/shm/pa194-paeq-ordinal-params-replay /dev/shm/pa194-paeq-ordinal-values-replay \
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
