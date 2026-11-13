# Historical-parent standard-iPRA extension: toy-tested only

These scripts are a separate historical-basis fork of the
[current-source extension](../extension/). They do not change that stricter
workflow. Their purpose is to permit an extension of a completed matched
frozen parent after its workspace sources have changed. **The resulting claim
would concern the historical parent snapshot and separately versioned added
sources; it would not be a current-source result.**

The freezer requires a strict, non-manifest-only `historical` plan, the exact
matched parent state, and its separately observed successful coordinator exit.
It copies the frozen parent source prefix unchanged, then the new sources in
dependency order. The preparer independently reruns the parent comparison,
checks declared against recorded direct dependencies and project ancestry,
and copies each matched sibling's own artifacts into separate seed trees.
The builders and comparator retain actual Lean dependency, companion,
hardlink-isolation and four exact report-name checks.

`verify_historical_sources` verifies the parent and extension snapshots and
their exact source-prefix identity. It uses a single `git cat-file --batch`
per commit to hash every parent source and Lake/toolchain configuration at the
parent manifest's pinned Git commit, and all added sources, configuration and
task policy at the separately pinned addition commit. It rejects non-commit
objects, unsafe or duplicate paths, symlinked source/configuration ancestors,
changed added workspace files, and incorrect source-basis labels. Both commits
and their source blobs must be locally available; the current workspace must
remain tracked and clean for the involved paths. Parent workspace bytes may
differ from the pinned historical bytes, but added bytes must remain identical.

The [control receipt](control-receipt.json) records ten historical
source/Git/symlink controls, nine selection controls, a Git-backed freezer,
an adversarial real-Lean toy pair, and an end-to-end toy that actually observes
the parent and freezer exits before the extension pair. The separate
[terminal observation](control-observation.json) records the outer test
runner's exit 0. These use toy sources and a synthetic Foundation provider;
they do not validate the real AQ29 parent, `IPRAStandardTheory`, or its client.
An [independent review](../../../reviews/ipra-standard-aq29-historical-independent/README.md)
reran the toy controls, checked the historical-basis guards, and verified all
1,210 source hashes and both configuration hashes in the parent manifest
against its pinned Git commit. It did not rehash the real frozen snapshot or
establish the real proof. No actual historical AQ29 extension has
been prepared or run. The existing parent build remains in progress, its
Foundation wrapper exit was not captured, and package-transitive, dynamic and
transient-mutation ancestry remains outside the stated guarantee.
