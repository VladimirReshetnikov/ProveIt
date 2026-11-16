`PA194PAeqQFCongruence.replace` proves a full model-uniform quantifier-free PAeq formula replacement theorem. In every candidate PRA model whose arithmetic reduct satisfies IΣ₁, if a and b are internally valid closed PAeq terms and p is an internally valid arity-one PAeq formula satisfying the existing `InternalQuantifierFree` coded-descendant predicate, modeled ordinaryPAeq provability of a = b entails modeled provability of p[a] → p[b]. Formula, term and proof codes may be nonstandard. The proof performs Σ₁ structural induction using the Π₁-defined quantifier-free predicate and its child/no-binder lemmas, separately replayed positive and negative equality-atom replacement, and Boolean implication closures. The numerical descendant predicate tracks the shared formula code constructors; its PRA/IΣ₁ infrastructure is used without assuming the model satisfies PA.

The conclusion is existence of a modeled proof, not a fixed proof-code function. The theorem excludes formulas with internally coded quantifier descendants and does not supply full PA induction, physical synchronization or an iPRA consistency implication. The audit rebuilds the new source and two-report top against the repository-source-replayed logical closure, atomic and term baselines plus the retained quantifier-free descendant overlay `/dev/shm/pa194-full-one-level-audit` and other dependencies. Foundation and workspace dependencies are prebuilt, including `/dev/shm` as an object root; it is not a clean whole-workspace build. The replay output `/dev/shm/pa194-paeq-qf-congruence-replay-v2` passed two clean reports. An earlier attempt with `/dev/shm/pa194-opening-substitution-repo` ahead of the descendant overlay caused Lean to segfault; that attempt is inconclusive and this command omits that overlay. From the repo root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-qf-congruence.sh "$PWD" NEW_EMPTY_OUTPUT \
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
