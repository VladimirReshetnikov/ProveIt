# PAeq ordinal interpretation parameter packets

`shiftTerms` maps an internally coded target-term vector under a new binder; its fixed parameter-free Σ₁ graph, length and indexed-element equations, and scope preservation hold in every arithmetic IΣ₁ model. `parameters` stores bound-term environment, free-term environment, and result term. The free vector's length is explicitly independent of the source bound arity. `childParameters` shifts both environments once and chooses result bound variable 0; `binaryParameters` shifts them twice and chooses result bound variable i. Their fixed Σ₁ graphs and internal scope preservation are proved, with `i < 2` required for binary validity. These results cover arbitrary, possibly nonstandard model-valued indices and packet codes satisfying the explicit validity premises; no ambient PA model assumption is used.

The packet operations are prerequisites for the parameter-changing PAeq-term-to-relational-source translator. They do not establish recursive totality/uniqueness for arbitrary terms, connect a coded interpretation to PAeq proofs, supply arithmetic axiom proofs, or prove the PA-to-source compiler. In particular Foundation's standard `Language.TermRec` passes the same parameter to children; the unary/binary packet change here must be integrated into a separately justified parameter-changing recursion.

The incremental audit rebuilds the parameter module and an eight-report audit top in one fresh output against the independently replayed ordinal-value and source-template modules and retained compiler overlays. Foundation and remaining workspace dependencies are prebuilt; this is not a clean whole-workspace build. Reproduce from the repo using an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-paeq-ordinal-params.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-paeq-ordinal-values-replay /dev/shm/pa194-source-template-replay \
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
