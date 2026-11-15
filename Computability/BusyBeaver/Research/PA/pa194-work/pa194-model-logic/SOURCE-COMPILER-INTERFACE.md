# Conditional internal PA-refutation compiler interface

`internalRefutationCompiler M hr` is the explicit proof-code obligation: for each internal code d of a PA proof of the quoted arithmetic falsum, there exists an internal code e of a falsum proof in `adjunctiveFullSepTheory`. `InternalCompiler` requires this in every candidate PRA model with an IΣ₁ arithmetic reduct, including nonstandard d and e. It asserts existence only; it does not itself construct a particular computable translation or prove the obligation.

`sourceCalibration_of_internalCompiler` discharges the prior bridge's `SourceCalibration` under that obligation, using the existing `PA195RefutationBridge.mapped_refutation_iff` to pass from the mapped PA-refutation sentence to an actual internal coded PA proof. `physical_nonhalt_consistency_of_internalCompiler` combines it with the explicit all-model `SchedulerToPhysical` assumption to derive, in formal standard iPRA, `¬Halt(PA194) → Con(PA)`. Both compiler and physical synchronization assumptions remain unproved meta-level hypotheses. Standard typed source-axiom identity alone does not discharge the nonstandard proof-code compiler.

The incremental checker rebuilds this interface and a two-report axiom audit in a fresh output against the independently replayed conditional iPRA bridge and retained dependencies. Its selected full-one-level baseline supplies the `PA196` and `M6` namespace roots to avoid shadowing by the partial scheduler-fairness namespace. The IΣ₁ transfer, refutation bridge, Foundation and other workspace dependencies remain prebuilt; this is not a clean whole-workspace build. Reproduce from the repo with an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-source-compiler-interface.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-full-sep-ipra-replay /dev/shm/pa194-full-sep-theory-replay \
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
