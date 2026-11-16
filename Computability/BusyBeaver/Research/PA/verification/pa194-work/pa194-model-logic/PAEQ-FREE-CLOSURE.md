This package defines fixed Σ₁ free-index bounds for arbitrary internally coded PAeq terms and formulas, including nested functions and nonstandard syntax. The term-vector bound uses the maximum over all children. It proves by model-internal structural induction that binding free variable zero decreases the term and formula bounds exactly by one, with truncated subtraction; the proof handles arbitrary model-valued vector lengths via `listMax_pred`.

`close_freeBound` proves that after `n` model-valued closure steps, the formula bound is the original bound minus `n`. `formulaFreeBound_zero_shift` proves that bound zero implies free-variable shift invariance, including for nested terms. Thus `close_closed` proves that an internal arity-zero PAeq formula closed at least its computed free bound remains arity zero and is shift-invariant. All results hold in every arithmetic IΣ₁ model; no full-PA assumption is used.

This establishes nonstandard coded closure correctness, but does not by itself identify the computed bound with a standard typed formula's `fvSup`, equate the operation with typed `univCl`, construct the PAeq induction-axiom code, or define the Δ₁ classifier of `ordinaryPAeq`. The single-output audit rebuilds six modules and a twelve-report top against the separately source-replayed PAeq closure and repository-source-replayed term binder plus retained overlays. Foundation and other workspace dependencies are prebuilt; this is not a clean whole-workspace build. From the repository root, using a fresh unused output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-paeq-free-closure.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-paeq-closure-repo /dev/shm/pa194-paeq-bind-term-repo \
 /dev/shm/pa194-paeq-term-formula-tree-repo \
 /dev/shm/pa194-term-formula-paeq-baseline \
 /dev/shm/pa194-paeq-ordinal-params-replay /dev/shm/pa194-paeq-ordinal-values-replay \
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
The original output `/dev/shm/pa194-paeq-free-closure-replay` passed with twelve clean axiom reports.
