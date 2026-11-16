# Conditional iPRA bridge for parameter-closed separation

`PA194FullSepIPRA` connects the parameter-closed source compiler and modeled scheduler to the existing one-way IΣ₁-to-iPRA transfer. It exposes two independent all-model assumptions:

* `SourceCalibration` says that in every candidate PRA model whose arithmetic reduct satisfies IΣ₁, model satisfaction of the mapped PA-refutation sentence yields an internal refutation of `adjunctiveFullSepTheory`. It must cover nonstandard PA and source proofs; the standard typed separation-schema identity by itself does not supply it.
* `SchedulerToPhysical` says that in every such model, an internal halt of the modeled scheduler implies satisfaction of the pinned PA194 physical halting sentence. It must cover nonstandard times and is not established by a standard-run simulation or a finite controller prefix.

`source_refutation_to_scheduler` proves the model-level implication from the first assumption using the separately checked full-separation compiler and fairness endpoint. `modeled_nonhalt_implies_PA_consistency` applies `ConPA.Directions.ipra_nonhalt_implies_consistency` to conclude that the formal `standardTheory` proves modeled nonhalting implies `nativePAConsistency`, conditional on `SourceCalibration` alone. `physical_nonhalt_implies_PA_consistency` applies the same transfer to the pinned `PA194ExplicitEndpoint.haltSentence`, conditional on both assumptions. The modeled halt sentence here is defined explicitly from `haltAfter` and one; no identification with a different syntax is assumed.

These are Lean-checked object-theory derivations under *meta-level all-model hypotheses*, not unconditional iPRA implications. They establish only the nonhalting-to-consistency direction; they do not prove either all-model assumption, the physical synchronization, or the PA194 equivalence. The underlying transfer uses its separately formalized candidate-PRA conservation and negative-translation results; its model assumptions include IΣ₁ and do not assert IΣ₁ itself is an iPRA axiom.

The incremental checker rebuilds the wrapper and a three-report axiom audit in a fresh output against the separately source-replayed parameter-closed compiler and its retained dependencies. The namespaces `PA196` and `M6` are linked from the selected full-one-level baseline to avoid an incomplete namespaced directory in the scheduler-fairness overlay shadowing later dependencies. The IΣ₁ transfer, physical endpoint, Foundation, and other workspace dependencies remain retained/prebuilt; this is not a clean whole-workspace build.

Reproduce from the repo using an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-full-sep-ipra.sh "$PWD" NEW_EMPTY_OUTPUT \
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
