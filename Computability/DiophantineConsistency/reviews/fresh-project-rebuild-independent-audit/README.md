# Independent audit of the fresh-project replay preparation

[`audit.py`](audit.py) saves exact copies and hashes of the source-closure
preparer, builder, comparator, pair runner, snapshot auditor and control tests.
It executes the copied controls and repeats the point-in-time source audit of
the pinned 1,210-module snapshot without overwriting its earlier observation.
Results and exact tested source hashes are in [receipt.json](receipt.json);
the source audit is [source-audit.json](source-audit.json).

The reviewed design creates an empty project object root, requires the Lean
compiler hash from the Foundation input manifest, rejects project fallback
artifacts, checks compiler-reported direct dependencies against each frozen
source's declared imports, checks declared Foundation inputs against the new
provider, and guards source, companion and output identities. The checks cover
the toy scenario and explicitly exercised negative controls, not every possible
runtime behavior.

This is **not** a full 1,210-module build, an independent proof replay, or an
authentication of transitive package inputs, dynamic imports, transient
mutations or the toolchain. The source scan is line based; comparison against
the compiler's direct dependency report happens only for rows that are actually
compiled. Any future full run requires its own observed completion and paired
comparison under an explicitly stated provider boundary.
