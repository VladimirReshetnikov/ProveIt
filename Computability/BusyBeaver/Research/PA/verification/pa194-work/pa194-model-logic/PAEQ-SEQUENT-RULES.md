This package extends the source-replayed exact image-sequent construction and logical axiom-leaf compiler with concrete Foundation target derivations for the verum, conjunction, disjunction, weakening and cut rules. Every constructor has a fixed parameter-free Σ₁ graph and an exact target sequent-index theorem; all apply in arbitrary arithmetic IΣ₁ models and to model-valued, possibly nonstandard codes, for any Δ₁ target source-language theory.

The conjunction and disjunction rules require a valid source formula set and actual target derivations of their translated premise sequents. The verum and weakening rules additionally require a packet valid at arity zero and the explicit bound that each formula in the source sequent is below the free-vector length. Cut requires the cut formula to be internally scoped and both it and its coded negation below that length; it also requires actual target premise derivations for the two translated premise sequents. `translatedSequent_insert` and `translatedSequent_subset` provide the exact context identities needed by these rules.

The checked constructors are local rule simulations. This package does not yet supply quantifier or source-shift rule preservation, translated theory-axiom proofs, or an induction compiling arbitrary source proof codes, and does not establish any consistency implication. The single-output audit rebuilds these two modules and a seventeen-report top against the independently source-replayed sequent-axiom baseline and the parent agent's repository-source-replayed dispatcher baselines and retained overlays. Foundation and other workspace dependencies are prebuilt; this is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-sequent-rules.sh "$PWD" NEW_EMPTY_OUTPUT \
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
The original output `/dev/shm/pa194-sequent-rules-replay` passed with seventeen clean axiom reports.
