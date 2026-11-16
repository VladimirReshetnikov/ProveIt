# Conditional scheduler-to-packed-clock bridge

`SchedulerToPackedClock` is the concrete remaining synchronization hypothesis: in every candidate PRA model with an IΣ₁ arithmetic reduct, for each model-valued k at which the modeled scheduler's `haltAfter` returns one, there exists a model-valued (possibly different) time t at which the pinned machine's packed-clock `haltIndicator` returns one. `schedulerToPhysical_of_packedClock` converts this clock-code relation into the prior all-model `SchedulerToPhysical` assumption by the checked semantics of `PA194ExplicitEndpoint.haltMatrix`. `physical_nonhalt_consistency_of_packedClock` combines it with the separate `InternalCompiler` hypothesis to derive formal standard-iPRA `¬Halt(PA194) → Con(PA)`.

The clock-code relation and internal PA-to-source proof compiler are both explicit, unproved all-model hypotheses; this is a conditional endpoint, not proof of synchronization, an unconditional iPRA implication, or the desired equivalence. In particular the clock relation must handle nonstandard scheduler times and models, not just standard finite traces.

The incremental source replay rebuilds the wrapper and a two-report axiom audit in a fresh output against the independently replayed compiler-interface and iPRA bridge overlays and retained dependencies. `PA196` and `M6` namespaces are linked from the selected full-one-level baseline to avoid incomplete namespace shadowing. The physical endpoint, Foundation and remaining workspace dependencies are retained/prebuilt; this is not a clean whole-workspace build. Reproduce from the repo with an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-scheduler-clock.sh "$PWD" NEW_EMPTY_OUTPUT \
 /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-source-compiler-interface-replay \
 /dev/shm/pa194-full-sep-ipra-replay /dev/shm/pa194-full-sep-theory-replay \
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
