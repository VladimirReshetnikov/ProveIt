# Nineteen recorded producer receipts

This read-only checker selects the bounded subset of 19 inputs identified by
the [141-input triage](../trace75-upstream-141-inventory/README.md): they are
not among the 16 exact stage outputs in the six larger runs, their earlier
captured output companions match the final selection, and a candidate receipt
records comparisons for all selected project imports. The selection and full
per-module evidence are in `observations/attempt01/stdout`.

For each of the 19, `check.py` verifies the pinned candidate receipt, exit 0,
unchanged recorded pins and direct-import lists, an output `.olean` at the
actual final selected realpath with the recorded hash, the captured source
snapshot and producer source-copy hashes, and both retained log hashes. It
also compares the source's explicit imports with the selected serialized
header and checks every recorded explicit import `.olean` hash against the
final selection. There are 56 such explicit edges: 52 project edges and four
Mathlib outside edges. The outside edges belong to `DirectBFSKernelBound`,
`DirectBFSKernelDivisibility`, `DirectBFSKernelLowerBound` and
`DirectBFSKernelLowerMassAlias`. The output records producer and selected
realpaths separately, so equality of hashes is not conflated with equality
of producer paths.

These historical receipts record `.olean` hashes for those direct imports,
not complete companion bundles. The implicit `Init` header entry is not in
those explicit receipt lists. Matching the four Mathlib `.olean` hashes does
not authenticate package-time transitive or dynamically loaded dependencies.
This packet does not authenticate the other 122 inputs, the full upstream
source/object closure, or an independent Lean replay; the original endpoint's
ancestry and file-binding limitations remain.

Author attempt01 exited 0. Checker SHA-256 is
`2195352d4a31e84e49e74b37f2cf322e3dedf30b989b4dc158525ceba3ad809b`,
terminal SHA-256 is
`9f5bc341d45234f151319ea2a113f181184debc7a89bca201491bd7151b56ba7`,
and stdout SHA-256 is
`d9e3020b3a928aefdbc7c4601a023c6f1b40d0930d4ad4f5229d4eac36555eb3`.
The [independent receipt audit](../../reviews/trace75-upstream-19-provenance-independent/README.md)
rechecked the subset, records and 56 comparisons without establishing the
omitted implicit, companion or transitive ancestry. No Lean was invoked.
