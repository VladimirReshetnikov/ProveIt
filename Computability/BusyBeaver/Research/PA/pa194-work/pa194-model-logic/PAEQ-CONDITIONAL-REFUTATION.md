`conditional_compile` uses Σ₁ induction over an arbitrary model-valued Foundation PAeq derivation, in an arbitrary arithmetic IΣ₁ model. Given any Δ₁ PAeq theory `U`, any Δ₁ source-language target theory `T`, a packet valid at arities zero, and a free-vector length greater than the source derivation code, it constructs an actual `T`-derivation of the exact translated image of the input sequent. The proof handles identity/axiom leaves, verum, conjunction, disjunction, weakening and cut using the previously replayed concrete coded rule constructors. The derivation-code bound propagates to every premise, every formula in a premise sequent, and both polarities of a cut formula.

Four fields of `RemainingRules U T param` remain explicit unproved assumptions: target derivability for universal introduction, existential introduction, the source free-variable shift rule, and translated source-theory axioms. Each of the first three consumes an already compiled target premise, while the theory field supplies the required target sequent from an actual internal U-axiom. `conditional_refutation` chooses `rootParameters d`, whose free vector has length `d+1`, maps singleton falsum exactly to singleton falsum, and concludes that a model-valued `Proof U d ⊥` yields some `Proof T e ⊥` under those same four assumptions. This is an existence result, not a fixed-graph proof-code transformer, and it does not prove the suppliers or the final consistency implication.

The theory `U` is still a parameter in this theorem. A subsequent [uniform Δ₁ classifier for `ordinaryPAeq`](PAEQ-ORDINARY-CLASS.md) is now proved, including its class equation for nonstandard codes. Instantiation still requires the four rule and theory suppliers and the separate arithmetic-PA-to-PAeq finite-axiom and induction suppliers. The induction bridge cannot use direct code equality: the arithmetic translation writes successor as addition by one, while the PAeq induction scheme uses primitive successor; transporting arbitrary properties requires a proof of their equivalence and congruence. No ambient model of full PA is assumed.

The single-output audit rebuilds both source modules and a five-report audit top against the parent agent's repository-source-replayed closed-root, sequent-rule, sequent-axiom, negation and formula-dispatcher baselines, plus retained overlays. Foundation and other workspace dependencies are prebuilt; this is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-conditional-refutation.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-closed-root-formula-repo /dev/shm/pa194-sequent-rules-repo \
 /dev/shm/pa194-sequent-axiom-repo /dev/shm/pa194-formula-negation-repo \
 /dev/shm/pa194-formula-dispatcher-repo \
 /dev/shm/pa194-term-scope-repo \
 /dev/shm/pa194-term-dispatcher-repo \
 /dev/shm/pa194-paeq-term-formula-tree-repo \
 /dev/shm/pa194-term-formula-paeq-baseline \
 /dev/shm/pa194-multiplication-code-repo /dev/shm/pa194-addition-code-repo \
 /dev/shm/pa194-paeq-template-compose-repo \
 /dev/shm/pa194-paeq-ordinal-params-replay \
 /dev/shm/pa194-paeq-ordinal-values-replay \
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
The original output `/dev/shm/pa194-conditional-refutation-replay` passed with five clean axiom reports.
