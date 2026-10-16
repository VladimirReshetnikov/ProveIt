Post-validation archive helper for repaired reuse135 source 703b85dbbc3a2b897d9f77e854b89eefed6efb8f.

This is a narrow successor of /tmp/gowers-reuse135-archive-tools/archive.py.
The sole executable change is the exact source-commit pin. Native common.py,
capture.py, run.py and original plan remain pinned byte-exact. Every guard,
sequential receipt check, current-artifact check and exclusive copy is unchanged.
No source, native, cache or repository mutation is performed by the helper.

After the actual three repaired commands pass, supply their real pins:

python3 /tmp/gowers-reuse135-archive-tools-repaired703b/archive.py \
  --snapshot /tmp/gowers-reuse135-repaired703b-source-snapshot.json ACTUAL_SNAPSHOT_SHA \
  --source-ledger /tmp/gowers-reuse135-repaired703b-applied-source-scope-review.json ACTUAL_LEDGER_SHA \
  --core /tmp/gowers-reuse135-repaired703b-core-attempt1/receipt.json ACTUAL_CORE_SHA \
  --shared /tmp/gowers-reuse135-repaired703b-shared-attempt1/receipt.json ACTUAL_SHARED_SHA \
  --supplemental /tmp/gowers-reuse135-repaired703b-supplemental-attempt1/receipt.json ACTUAL_SUPPLEMENTAL_SHA \
  --output /tmp/gowers-reuse135-repaired703b-archive-attempt1

Root may add --extra-evidence ACTUAL_MANIFEST ACTUAL_MANIFEST_SHA to preserve the
failed earlier core, diagnostic logs and reviewed same-length two-body repair.
The old extra-evidence manifest is intentionally not copied as current evidence.
Actual snapshot, ledger, runtime receipt and extra-evidence hashes remain mandatory
runtime inputs, not fabricated success placeholders. Run before inventory or
publication edits: the current source and HEAD guard must still pass.

The output retains one actual command result for each core/shared/supplemental
invocation. Its 76 per-root closure rows are metadata, not invented per-root native
results. Original source, receipts, logs and tools remain unchanged. The earlier
README remains the full unchanged schema reference. No entrypoint or native/Git
operation was invoked during preparation; only AST/text checks and a read-only
HEAD identity check were performed.
