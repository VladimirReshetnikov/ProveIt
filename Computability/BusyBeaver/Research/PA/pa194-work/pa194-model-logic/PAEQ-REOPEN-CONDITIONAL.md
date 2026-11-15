The explicit `OpeningInverse` hypothesis says `free language (bindFormula 0 p) = p` for every internally scoped zero-arity PAeq formula p. Assuming this hypothesis, `reopen` uses the real Foundation modeled proof rules to specialize one closed formula and `reopen_iterated` uses a Sigma-1 induction to remove an arbitrary model-valued number of closures. These yield modeled proofs of the primitive and add-one induction bodies for every internally valid arity-one property, and a modeled proof of the PAeq translation of the arithmetic induction body for any valid arithmetic property and any translation parameter. This includes nonstandard codes. Independently, the zero-free-bound theorems discharge the body result without OpeningInverse when the explicitly computed bound is zero.

OpeningInverse itself is NOT proved. The custom unbinder inverse does not yet identify it with Foundation `free`. The arithmetic result is for the induction body, not the full parameter-closed axiom, and no full compiler, physical synchronization, or native iPRA implication is claimed. These results assert modeled proof existence and do not supply a fixed proof-code function.

The audit rebuilds the two new modules and the seven-report audit against source-replayed repository baselines and retained prebuilt Foundation/workspace objects; it is not a clean whole-workspace build. From the repository root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-reopen.sh "$PWD" /dev/shm/pa194-paeq-reopen-conditional-repo \
 /dev/shm/pa194-paeq-induction-add-one-repo /dev/shm/pa194-paeq-induction-axiom-repo /dev/shm/pa194-paeq-universal-formula-repo /dev/shm/pa194-paeq-arithmetic-induction-repo /dev/shm/pa194-paeq-add-one-at-repo \
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
