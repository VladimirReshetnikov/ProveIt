# Checked native theory and model interface

The unchanged [NativeTheory source](Lean/ZFCinPA/NativeTheory.lean) passes a
fresh Lean check and **10 axiom probes with 11 typed clients**. The
[actual record](results/native-theory-verification.json) verifies its Δ₁
theory definition and extracts containers, global-image collection and raw
membership irreflexivity from an assumed nonempty model. All probes use
only standard Lean axioms.

The theory combines Foundation equality axioms, the fixed container and
irreflexivity axioms, and the universally closed two-slot GIC schema. The
collection theorem covers each standard repository formula and arbitrary
model-valued parameter environment; `models_cpgic` restricts it to the
equality-free matrices of the CP/GIC interface. Its support clause permits
witnesses outside the input set, as global-image collection requires.
This unit does not construct the later extensional quotient or well-founded
interpretation domain, prove model existence, or transport every internally
coded native axiom to the validator.

Source and audit took 4.557 and 1.942 seconds with default proof limits,
one compiler thread, 4,096 MiB and a shared 120-second deadline. The three
source warnings are an unused section assumption in `sat_of_models_toSet`
and two unused simplification arguments. The audit has no warnings.
The [source log](native-theory/source.log) preserves them unchanged.
All 362 recorded inputs and the fresh first-provider object remained
unchanged after the audit.

The guard selects 44 project modules from the exact actual Translation,
NativeGicDelta1, NativePeel and BootstrapFrameRotation240 records. Only
ZFDelta1 is selected from NativePeel, and only seven Profile modules from
the broad bootstrap record. Five opaque cached Foundation/Mathlib boundaries
and Init remain explicit. The sparse Foundation mirror preserves the six
selected Foundation project modules and their companions. Companions first
observed now are distinguished from captures made by earlier runs; unrelated
historical inputs are not promoted to current checked dependencies.

The [publication](results/native-theory-publication.json) and
[history](native-theory/history.json.gz) retain the pending-parent plan,
subsequent actual-parent guard, source snapshots, audit and raw logs. The
[independent source/API review](native-theory/peer-review.json) and its
[history](native-theory/peer-history.json.gz) describe the earlier prospective
provider checkpoint, before Translation's actual result was bound. They
are separate from the executed guard's result. This check closes one entry
in the original validator dependency inventory; the final PA endpoint remains
pending.
