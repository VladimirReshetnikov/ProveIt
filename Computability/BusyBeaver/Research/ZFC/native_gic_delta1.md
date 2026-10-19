# Checked native GIC schema recognizer

The unchanged [NativeGicDelta1 source](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeGicDelta1.lean)
and a focused [typed audit](native_gic_delta1_audit.lean) passed one fresh Lean
source/audit run: **7 named probes, 10 typed callers, zero warnings**. Source
and audit took 12.993 and 2.021 seconds. The [actual record](results/native-gic-delta1-verification.json)
and [independent review](results/native-gic-delta1-review.json) retain exact
source, snapshot, provider and fresh-object identities.

For arbitrary ordered-ring models of IΣ₁, the module identifies the typed and
raw GIC body, supplies a Σ₁ graph for its raw constructor, and proves a Δ₁
recognizer at arbitrary internal codes. Its quotation and code-bound results
on standard syntactic matrices supply the standard-membership part of the
stand-alone GIC theory's Δ₁ instance. The all-model properness obligation is
also proved. These are syntactic recognition results; this unit does not
prove arbitrary internal native axioms transport to ZF, nor an internal PA
consistency endpoint. NativeTheory, NativeInterp and NativeFixed are not
compiled by this run.

The successful audit prints the seven expected reports, each using only
`propext`, `Classical.choice` and `Quot.sound`. The source/audit pair shares
120 seconds with `-j1 -M4096` and default proof limits. The guard captures the
fresh object and its first-provider identity before audit, then checks the
inputs and selected providers again. It performs no compiler-version query,
dependency build or download.

The boundary contains four selected project pairs, three direct external
imports, two additional retained external discovery pairs and Init/Omega.
The 33 recorded inputs were rehashed in the independent review. The older
ConstructibleInterpretation parent lacks modern pre-audit fresh capture;
only its selected reused pairs and recorded snapshots are consumed. The
Foundation namespace overlay and remaining external library caches retain
their historical provenance limits and are not wholly re-attested. Exact
historical cached paths are required; this packet is not a clean-checkout
build procedure and distributes no compiled objects.

[Exact text history](results/native-gic-delta1-history.json) preserves the
original guard and boundary, successful preparation and actual logs,
source/audit snapshots, author and independent metadata reviews, and the
original supplied `NativeTheoryAudit.lean`. That historical audit imports the
broader NativeTheory and contains five probes with no typed callers; it was
not selected or executed here. A reviewer-only descriptor-shape correction
is retained separately from proof history. There was no failed proof attempt
or source repair in this unit.

The installed guard changes only path discovery and the repository,
source/audit/boundary defaults; the dependency root remains pinned. Run from
this directory with the exact recorded providers available:

```sh
python3 -B check_native_gic_delta1.py --prepare-only --output /tmp/native-gic-prepared
python3 -B check_native_gic_delta1.py --output /tmp/native-gic-actual
```

The installed defaults passed a [preparation-only check](results/native-gic-delta1-maintained-preparation.json)
with no compiler invocation. The [publication record](results/native-gic-delta1-publication.json) records
those default substitutions, exact history contents and roles. The original
module's upstream authorship is unchanged; the focused audit/guard were
prepared by Opening, root executed the proof, and Reflection independently
reviewed the evidence and prepared this publication proposal.
