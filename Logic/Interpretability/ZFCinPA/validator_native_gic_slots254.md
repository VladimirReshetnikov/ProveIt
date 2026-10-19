# Native GIC matrix slots and padding resources

[ValidatorNativeGicSlots254](Lean/ZFCinPA/ValidatorNativeGicSlots254.lean)
and its [typed audit](validator_native_gic_slots254_audit.lean) passed a fresh
Lean source/audit check: **8 named probes, 10 typed callers, zero warnings**.
The source took 3.572 seconds and the audit 2.839 seconds. The
[actual record](results/validator-native-gic-slots254-verification.json)
preserves the selected sources, commands, logs and pre-audit object identity.

For arbitrary internally typed two-slot matrices in the function-free set
language, the first two theorems identify the native GIC support and coverage
slot substitutions. Support uses the ordered labels `[t+6,t+4]`; coverage
uses `[t+4,t+6]`. These identities hold in every ordered-ring model of IΣ₁.
They reuse the checked internal simultaneous-substitution theorem.

The padding code `pad p` is even. Under IΣ₂, odd free labels, two odd matrix
labels and an odd binder stream therefore keep that code vacant in the encoded
matrix, including the encoder's fallback label 1. The matrix and its labels
are chosen before padding, avoiding a circular freshness choice. The final
theorem supplies a `CProv` proof of the literal padded validator GIC instance.

This work applies to the unchanged logical source shared by the 243-, 242-
and 241-state candidates. The complete Foundation native-body encoding,
alpha transport, arbitrary universal closure, internal proof translation and
PA consistency endpoint remain separate obligations. No smaller machine
bound follows from this helper alone.

The first actual attempt failed: one unnecessary-`simpa` warning and the
unclosed numeric side condition `1+1=2`. The successor changes only those
two proof terms, retaining the statements and audit. The
[exact history](results/validator-native-gic-slots254-history.json) preserves
both attempts, raw logs, preparations, sources, guards, snapshots, repair and
reviews. Compiled objects and cache symlinks are recorded but not distributed.

The successful attempt used one shared 120-second source/audit budget,
`-j1 -M4096` and default proof limits. Its eight axiom reports contain only
`propext`, `Classical.choice` and `Quot.sound`. The guard captures the fresh
first provider before audit and rechecks all selected inputs afterwards.
It performs no compiler-version query, dependency build or download.
The boundary selects 31 project source/object pairs, six direct external
pairs plus the inherited Seq pair, and Init/Omega: 147 recorded inputs and
40 first-provider checks. The Foundation overlay remains a supplied cache
boundary, without a claim about the whole cache.

Three modern actual parents and the historical environment-vacuity parent
supply the dependencies. That historical parent retains two unused-section
warnings, per-command 120-second limits, a recorded compiler-version query
and no modern first-provider capture. The new unit does not erase those
limitations. Its [evidence review](results/validator-native-gic-slots254-review.json)
explicitly discloses that Opening authored the source, audit, guard and
repair. Root independently read and executed the attempts; Reflection
reviewed the source, guard and repair. The author's evidence review is not
represented as independent authorship.

The maintained guard changes four path defaults only. With the exact
historical cached inputs available, run from this directory:

```sh
python3 -B check_validator_native_gic_slots254.py --prepare-only --output /tmp/validator-native-gic-slots254-prepared
python3 -B check_validator_native_gic_slots254.py --output /tmp/validator-native-gic-slots254-actual
```

[Publication metadata](results/validator-native-gic-slots254-publication.json)
records the mappings and installation check. This is not a clean-checkout
rebuild procedure; the recorded cached dependencies are prerequisites.
