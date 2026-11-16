# Initial PAeq ordinal-value source codes

`PA194OrdinalTemplateRew` proves current-Foundation typed substitution naturality for the relational ordinal `domain`, `zero`, and `successor` formulas. The proof adapts the corresponding upstream rewriting laws, including explicit preservation of bound slots under nested binders.

`PA194PAeqOrdinalValues` instantiates the separately source-replayed one- and two-term template graphs for ordinal-domain, zero, successor, and primitive source equality. It proves exact typed quotation and internal scoped validity for each instantiated formula. The variable-value and zero-value formulas and the one-step successor-value formula have explicit parameter-free Σ₁ arithmetic graphs, graph instances, scoped validity and exact typed quotation. The successor clause receives the already translated child under one further binder and shifts the result term using Foundation's coded bound-variable shift. All model-valued inputs, including nonstandard codes, are covered by the graph/validity results in every arithmetic IΣ₁ model; no model-of-PA assumption is made.

These are the base and unary syntactic clauses needed by the PAeq-to-relational-source interpretation. They do not construct a recursive translator over arbitrary PAeq terms, prove addition/multiplication value constructors or their relational semantics, translate PAeq formulas or proofs, supply PA axiom derivations, or establish the internal PA-to-source compiler. Typed quotation results concern standard typed syntax; they do not alone prove recursive correctness on nonstandard source terms.

The incremental source audit rebuilds both modules and a 14-report audit top in one fresh output against the separately replayed source-template, uniform-closure and compiler overlays. Foundation, the ordinal-domain source and other workspace dependencies remain prebuilt; this is not a clean whole-workspace build. Reproduce from the repo with an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-paeq-ordinal-values.sh "$PWD" NEW_EMPTY_OUTPUT \
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
