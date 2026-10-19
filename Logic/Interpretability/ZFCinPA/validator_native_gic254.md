# Literal internal GIC introduction

[ValidatorNativeGic254](Lean/ZFCinPA/ValidatorNativeGic254.lean) and its
[typed audit](validator_native_gic254_audit.lean) passed a fresh Lean source/audit
check: **8 named probes, 10 typed callers, zero warnings**. The selected run
used 2.509 seconds for the source and 2.025 seconds for the audit. The
[actual record](results/validator-native-gic254-verification.json) and
[author-disclosed evidence review](results/validator-native-gic254-review.json)
retain the exact source, snapshots, provider identities and pre-audit object.

For every ordered-ring model of IΣ₁ and every internal matrix value `p`, the
unit extracts the literal C/G formulas from the checked validator bundle.
It defines `pad p := ¬¬p`, proves actual `CProv` implications both ways and
proves `pad p > 3`. This supplies the bundle's numeric side conditions at
labels 1 and 3, even for `p = 0`, and gives a `CProv` proof of the literal G
instance with both matrix and witness label `pad p`. A final theorem closes
the domain label 3. It does not close every free parameter.

This is a literal validator formula theorem. Identifying it with the
configurable encoding of an arbitrary internal Foundation GIC matrix still
requires simultaneous substitution, capture avoidance and alpha transport.
General universal closure, all native-axiom cases and the internal derivation
translation to `CProv 1` remain separate. The unit establishes no new machine
state bound or internal PA consistency endpoint.

The first actual source attempt failed at the numeric proof of `3 < 4`:
`simp` made no progress. It produced no successful module or audit run.
The successor changes only that proof term to use `lt_add_one` and
`three_add_one_eq_four`. The statements and audit are identical; the renamed
boundary is byte-identical, and the guard changes only the selected source
hash and the source/boundary paths. [Exact history](results/validator-native-gic254-history.json)
preserves both preparations, the failed and successful raw records/logs,
original and successor sources/guards, snapshots, numeric repair and reviews.

Each source/audit attempt shares 120 seconds, with `-j1 -M4096` and default
proof limits. The successful audit reports only `propext`, `Classical.choice`
and `Quot.sound`. The guard records the fresh object and its first-provider
identity before audit and rechecks all inputs afterwards. It performs no
compiler-version query, dependency build or download.

The exact [QuantifierCore parent](validator_quantifier_core254.md) supplies
21 selected project source/object pairs including its fresh module. Three
direct external import pairs, the inherited Seq pair, and Init/Omega remain
pinned. The 74 current inputs were checked in the evidence review. The
historical parent provides its own pre-audit object hash but lacks the newer
first-provider capture; that limitation is preserved. The external caches
are supplied boundaries and are not wholly re-attested. Exact historical
cached inputs remain prerequisites; no compiled objects are distributed and
this is not a clean-checkout rebuild procedure.

The installed guard changes four path defaults only. From this directory,
with the recorded inputs available:

```sh
python3 -B check_validator_native_gic254.py --prepare-only --output /tmp/validator-native-gic254-prepared
python3 -B check_validator_native_gic254.py --output /tmp/validator-native-gic254-actual
```

The installed defaults passed a [preparation-only check](results/validator-native-gic254-maintained-preparation.json),
with no proof compilation. [Publication metadata](results/validator-native-gic254-publication.json)
records the byte mappings, default changes and history. Opening authored the
source, audit, guard, numeric repair, evidence review and packaging proposal;
the evidence review explicitly discloses that role. Root independently read
and executed the proofs and reviews publication. No independent authorship is
claimed for the author-side evidence review.
