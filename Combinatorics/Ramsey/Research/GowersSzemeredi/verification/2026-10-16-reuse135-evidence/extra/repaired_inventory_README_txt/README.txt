Inventory comparator for repaired reuse135 source 703b85dbbc3a2b897d9f77e854b89eefed6efb8f.

This is a narrow successor of /tmp/gowers-reuse135-inventory-comparison-tools/compare_inventory.py.
Only SOURCE_COMMIT and the local BASE directory change. Every function, including
normalize, array_order, differences, verify_locations and main, is byte-exact.
The published baseline and generator copies are byte-exact. No count, ordering,
duplicate, alias, source-location, receipt or chronology requirement is relaxed.

Use only after the actual repaired core603, shared1904 and supplemental351
commands have passed and the unchanged generator has actually run afterward:

python3 /tmp/gowers-reuse135-inventory-comparison-tools-repaired703b/compare_inventory.py \
  --raw ACTUAL_RAW --raw-sha256 ACTUAL_RAW_SHA \
  --generator-receipt ACTUAL_GENERATOR_RECEIPT --generator-receipt-sha256 ACTUAL_GENERATOR_RECEIPT_SHA \
  --supplemental-receipt ACTUAL_SUPPLEMENTAL_RECEIPT --supplemental-receipt-sha256 ACTUAL_SUPPLEMENTAL_RECEIPT_SHA

Default is read-only. After inspecting the result, --write --output-dir /tmp/NEW_DIR
writes only exclusive raw.json, normalized.json and comparison.json. All 120 ordered
rows, full objects, occurrence counts and multiplicities must remain exact apart
from reported file/line leaves. Ambiguous duplicates require an inspected explicit
mapping under the unchanged parser. No runtime result is prefilled or inferred.
Native receipts are referenced and shape/chronology checked, not replayed here.
The predecessor README remains the complete unchanged algorithm/schema reference.
No entrypoint, generator, Lean, native, cache, repository or Git mutation was run
during preparation. AST parsing and exact text comparisons only.
