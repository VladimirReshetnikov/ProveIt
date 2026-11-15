`PA194RootFormula` defines a fixed Σ₁ graph for a root packet whose bound-term vector is empty and whose free-term vector consists of `p+1` copies of a fixed source free variable. This provides the conservative lookup bound for translating source formula code `p`. For any model-valued PAeq formula of bound arity zero in an arithmetic IΣ₁ model, `rootFormula p` has target bound arity zero; `rootFormula` maps falsum to falsum. Arity zero alone does not assert absence of free variables.

`PA194ClosedRootFormula` applies the previously source-replayed model-valued free-index bound and iterated closure to this root translation. Its fixed parameter-free Σ₁ graph is uniform in arithmetic IΣ₁ models. For every candidate PRA plus IΣ₁ model, `closedRootFormula_sentence` proves that a model-valued PAeq formula of bound arity zero, including nonstandard codes, yields a target formula of bound arity zero invariant under free-variable shift. `closedRootFormula_falsum` proves exact preservation of falsum. This uses the previously checked model-specific closure/free-bound results and does not assume a model of full PA.

These are syntactic outputs. In particular, no theorem here says closure preserves derivability from translated hypotheses, translates PA axioms, or constructs a PAeq proof-code transformer. Generalization and translated assumptions must be handled by the future proof compiler. The single-output audit rebuilds the two modules and nine-report top against the parent agent's repository-source-replayed formula dispatcher, source-replayed closure/free-bound baselines, and retained overlays. Foundation and other workspace dependencies are prebuilt; this is not a clean workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-closed-root.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-formula-dispatcher-repo /dev/shm/pa194-term-scope-repo \
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
The original output `/dev/shm/pa194-closed-root-formula-replay` passed with nine clean axiom reports.
