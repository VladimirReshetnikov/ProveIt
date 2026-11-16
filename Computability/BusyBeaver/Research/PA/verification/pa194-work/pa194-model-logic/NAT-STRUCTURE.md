# Standard natural arithmetic structure bridge

`induced_eq_canonical` proves equality of the complete `ORingStructure Nat` induced by the candidate-PRA standard model and the ordinary canonical Nat arithmetic structure. Zero, one and order coincide definitionally; addition and multiplication use the checked standard evaluations of their primitive-recursive codes. `fullSep_eval_bridge` transports the `fullSepUniform` arithmetic classifier evaluation at every standard natural q. `sigma_model_transport` is a general equality transport for propositions depending on an arithmetic structure together with an IΣ₁ model proof. The latter can transport dependent predicates and quotation expressions without equating proof terms manually.

The results concern the standard natural model and do not establish a source-theory identity, a model-uniform proof interpretation, a physical-machine correspondence, or a native iPRA theorem.

The incremental checker rebuilds this module and a three-report axiom audit in a fresh output against retained classifier and compiler overlays, with `PA196` and `M6` namespaced symlinks from the selected full-one-level baseline to avoid partial namespace shadowing. Foundation and other workspace dependencies remain prebuilt; this is not a clean whole-workspace build. Reproduce from the repository with an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-nat-structure.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-full-sep-theory-replay \
 /dev/shm/pa194-unclose-envelope-replay /dev/shm/pa194-uniform-fully-closed-replay \
 /dev/shm/pa194-uniform-closure-replay /dev/shm/pa194-fully-closed-replay \
 /dev/shm/pa194-model-separation-full-replay /dev/shm/pa194-model-separation-seeded-replay \
 /dev/shm/pa194-model-closure-definability-replay /dev/shm/pa194-model-closure-replay \
 /dev/shm/pa194-general-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 \
 /dev/shm/pa194-closed-sep-theory-replay /dev/shm/pa194-uniform-sep-combined-replay \
 /dev/shm/pa194-standard-no-free-replay /dev/shm/pa194-closed-sep-classifier-replay \
 /dev/shm/pa194-fairness-full-source-replay /dev/shm/pa194-generic-sim-replay \
 /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay \
 /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit \
 /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-general-shift-replay \
 /dev/shm/pa194-general-reverse-shift-replay /dev/shm/pa194-unrestricted-all-replay \
 /dev/shm/pa194-general-freshness-audit /dev/shm/pa194-observational-general-audit \
 /dev/shm/pa194-full-one-level-audit
```
