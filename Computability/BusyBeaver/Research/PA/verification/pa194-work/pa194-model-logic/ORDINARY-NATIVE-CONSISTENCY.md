`ordinary_matrix_exists` proves the existence of a fixed open PRA-language matrix q with two formal consequences: classical PRA proves `∀q ↔ lMap (∀¬bnd ordinaryRefutation)`, and the native intuitionistic `standardTheory` proves `¬native(∃¬q) → nativePAConsistency`. Here `ordinaryRefutation` is Foundation's arithmetized ordinaryPAeq-refutation predicate and `bnd` is the fixed bounded-witness transformation. In IΣ₁ arithmetic reducts, `∃bnd ordinaryRefutation` is equivalent to the modeled ordinaryPAeq refutation. The proof uses the unconditional model-level PA-to-ordinaryPAeq refutation transport and the existing one-way model-to-iPRA transfer. The matrix is obtained existentially by `unary_open`, rather than printed or connected to a machine in this result. Its native antecedent has not been identified with the direct native reading of ordinaryPAeq's consistency sentence. This does not prove PA consistency, PA194 nonhalting, physical synchronization, the ordinaryPAeq-to-source compiler, or the requested machine equivalence.

The audit rebuilds the source and a three-report axiom audit against the repository-replayed complete PA supplier and source-compiler interface, plus retained source, Foundation, and workspace objects. The selected namespace baseline supplies PA196 and M6. It is not a clean whole-workspace build. From the repository root with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-ordinary-native-consistency.sh "$PWD" /dev/shm/pa194-ordinary-native-consistency-repo \
 /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-source-compiler-interface-repo /dev/shm/pa194-paeq-complete-supplier-repo /dev/shm/pa194-paeq-finite-supplier-repo /dev/shm/pa194-paeq-finite-mullt-next-repo /dev/shm/pa194-full-sep-ipra-repo /dev/shm/pa194-full-sep-theory-repo /dev/shm/pa194-unclose-envelope-replay /dev/shm/pa194-fairness-full-source-replay \
 /dev/shm/pa194-paeq-finite-ltirrefl-next-repo /dev/shm/pa194-paeq-finite-lttrans-next-repo /dev/shm/pa194-paeq-finite-mulassoc-next-repo /dev/shm/pa194-paeq-finite-mulcomm-next-repo /dev/shm/pa194-paeq-finite-distr-next-repo /dev/shm/pa194-paeq-finite-addlt-next-repo /dev/shm/pa194-paeq-finite-onele-next-repo /dev/shm/pa194-paeq-finite-comm-next-repo /dev/shm/pa194-paeq-finite-lt-addeq-repo /dev/shm/pa194-paeq-finite-assoc-next-repo /dev/shm/pa194-paeq-finite-zerole-next-repo /dev/shm/pa194-paeq-finite-lt-addeq-repo /dev/shm/pa194-paeq-finite-eqrel-next-repo /dev/shm/pa194-paeq-finite-ext-next-repo /dev/shm/pa194-paeq-finite-remaining-repo /dev/shm/pa194-paeq-finite-transferred-repo /dev/shm/pa194-paeq-pa-except-finite-repo /dev/shm/pa194-paeq-induction-supplier-repo /dev/shm/pa194-paeq-add-one-proof-repo /dev/shm/pa194-paeq-ordinary-class-repo /dev/shm/pa194-paeq-induction-closure-reduction-repo /dev/shm/pa194-paeq-induction-body-supplier-repo /dev/shm/pa194-paeq-induction-reduction-repo /dev/shm/pa194-paeq-induction-image-repo /dev/shm/pa194-paeq-induction-add-one-repo /dev/shm/pa194-paeq-induction-axiom-repo /dev/shm/pa194-paeq-universal-formula-repo /dev/shm/pa194-paeq-arithmetic-induction-repo /dev/shm/pa194-paeq-add-one-at-repo \
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
