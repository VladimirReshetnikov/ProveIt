# Coded substitution into source templates

The two template operations instantiate any fixed standard typed relational-source formula with one or two model-valued term codes using Foundation's capture-aware coded substitution. `templateOneGraph` and `templateTwoGraph` are explicit parameter-free Σ₁ arithmetic formulas for these operations; their graph theorems hold in every arithmetic IΣ₁ model, including for nonstandard arguments. `templateOne_valid` and `templateTwo_valid` prove preservation of internal semiformula scope from the corresponding term scope. `templateOne_quote` and `templateTwo_quote` prove exact compatibility with typed quotation and substitution for standard typed terms.

These are syntax-level building blocks for adapting the upstream PAeq-to-relational-source interpretation. The fixed typed templates themselves are standard parameters; the results do not yet construct the ordinal domain, the complete PAeq term/formula interpretation, the required translated-axiom proofs, a PA proof-code compiler, or either machine-consistency direction. No ambient full PA model assumption is used.

The incremental source replay rebuilds the source and six-report audit top in one fresh output against the separately checked uniform-closure, fully-closed, compiler and classifier overlays. Foundation and other workspace dependencies remain prebuilt; this is not a clean whole-workspace build. From the repo, use an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-source-templates.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-uniform-fully-closed-replay /dev/shm/pa194-uniform-closure-replay \
 /dev/shm/pa194-fully-closed-replay /dev/shm/pa194-model-separation-full-replay \
 /dev/shm/pa194-model-separation-seeded-replay /dev/shm/pa194-model-closure-definability-replay \
 /dev/shm/pa194-model-closure-replay /dev/shm/pa194-general-separation-replay \
 /dev/shm/pa194-ranked-open-separation-replay-v3 /dev/shm/pa194-closed-sep-theory-replay \
 /dev/shm/pa194-uniform-sep-combined-replay /dev/shm/pa194-standard-no-free-replay \
 /dev/shm/pa194-closed-sep-classifier-replay /dev/shm/pa194-generic-sim-replay \
 /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay \
 /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit \
 /dev/shm/pa194-adjunctive-admission-audit /dev/shm/pa194-general-shift-replay \
 /dev/shm/pa194-general-reverse-shift-replay /dev/shm/pa194-unrestricted-all-replay \
 /dev/shm/pa194-general-freshness-audit /dev/shm/pa194-observational-general-audit \
 /dev/shm/pa194-full-one-level-audit
```
