# Comparison and audit artifacts

The comparison is pinned to ProveIt commit
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

## Portable novelty replay

From the archive root, run:

```sh
python3 comparison/verify_novelty.py construction/AX11QGH/machine/machine.tm --output ax11qgh_novelty_fresh.json
python3 comparison/verify_novelty.py construction/AX11HR/machine/machine.tm --output ax11hr_novelty_fresh.json
```

Only Python's standard library is needed. `representatives.json` and
`tables/*.tm` are all the comparison inputs: 177 distinct labeled 194-state
tables, including all 110 spanning catalog classes and two nonspanning
diagnostic tables. The checker verifies file hashes and compares exact
canonical tuples, allowing control renaming, every spanning root, global tape
reflection, symbol exchange, and ignored terminal halt actions. Symbol exchange
is a structural test, not a claim about preservation of zero-blank semantics.
The two nonspanning diagnostics are excluded by the invariant that a spanning
root exists for the new machines. Neither new candidate matches any input.

`ax11qgh_novelty_portable.json` and `ax11hr_novelty_portable.json` record fresh
successful executions of the packaged checker. The older `ax11gh_novelty.json`
and `ax11hr_novelty.json` record an earlier, unoptimized exact canonical
comparison. Both implementations return identical candidate fingerprints.
Historical execution paths recorded in receipts are provenance, not inputs
needed by the portable checker.

## Complete ledgers and sources

`frontier194_ledger.json`, `.csv`, and `FRONTIER194_LEDGER.md` list all 110
catalog classes with mechanism, source locator, attributed proof status, and
the actual scope of this review. The JSON/CSV representative paths point into
the included `tables/` directory. `packet_ledger86.json` and `.csv` cover 82
filed packets and four current incoming archives. `frontier193_ledger.json`
and `.csv` retain all 53 cataloged 193-state research candidates, with no
unsupported consistency or impossibility claim. `COMPARISON_NOTES.md`
explains the design axes, aliases, proof status, and negative-search limits.

The filed 13,006-table catalog was inherited from the pinned repository:
`MACHINES.tsv`, `MACHINE_FILES.tsv`, and `machine_classes.py`. All four current
incoming archives were freshly extracted and their literal `.tm` files parsed;
`incoming_literal_census.json` and `census_summary.json` retain that result.
This is an exhaustive literal-file count for the four archives, not an assertion
that every arbitrary JSON or prose table format was freshly parsed. The known
historical JSON-only N-AD candidate has a later literal export and is included.

`source_identity_manifest.json` gives both Git blob SHA1 and SHA256 identities
for the pinned index files and four incoming ZIPs, and hashes the delivered
descriptive metadata that was attributed. Source paths not included in this
compact comparison directory identify remote repository/archive members;
they are not runtime dependencies of the novelty replay.

## Written-proof audit

`AX11H_AUDIT.md` distinguishes the incoming packet's new written iPRA proof
from the incomplete Lean development. It records the arguments independently
inspected, representative source constructors checked, finite checks freshly
replayed, and limits of the review. `base_replay/` contains the fresh finite
verification summaries and selected literal/source-command receipts. The
complete inherited AX11H dependency archive is retained separately in the
main deliverable's `reference/` directory.
