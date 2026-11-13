# Twenty-eight graph-support overlay objects

This read-only triage identifies the 28 still-unclassified direct project
inputs whose final selected `.olean` realpaths are regular files in
`/tmp/compact44-graph-support-join-01/lib/DiophantineConsistency`. It pins
the earlier 141/19/ten-runner records and final assembly result, and rehashes
the selected objects and observed candidate sources/logs during the scan.
It invokes no Lean.

For **27 of 28**, a same-named `.lean` file exists at the overlay root,
matches exactly one current prototype source byte-for-byte, and its explicit
imports match the final selected serialized header. For
`ArithmeticPackingBlocks`, no same-named overlay source was found; the
current canonical workspace source has matching declared imports, but the
scanner cannot identify it as the selected object's producer source. These
are point-in-time source/header matches, not producer authentication.

**22 of 28** have at least one same-name overlay `.log` file; six do not.
Filenames alone do not link a log to the selected output. Seven prototype
directories contain an observation JSON with both the source hash and selected
output hash as text; none contains the exact final output realpath. They are
listed as candidate evidence only, not as verified production records. The
full object realpaths, source paths, log paths and candidate JSON hashes are
in attempt01 stdout.

Author tool session 73643 exited 0 and was reaped. Checker SHA-256 is
`2efe676d2fd92626cb878628f6cf948547fcce2c64b282f3effa339856a29fdf`,
terminal SHA-256 is
`6b2dcfae50c3ccee1f60657691cd809df9d15319508c16a06a83e476f95dcb5a`,
and stdout SHA-256 is
`a1f701226ce2c5c1f9eef7b627f4d6ce6aa494bc4689c846d8617f172d750570`.
The [independent triage audit](../../reviews/trace75-graph-support-28-triage-independent/README.md)
rechecked the source/header, log and candidate-record classifications without
inferring producer linkage.

The scanner does not reconstruct exact compile commands, tie those sources
or logs to these specific objects, authenticate producer-time direct inputs,
or establish a source-current or independent Lean replay. Package,
dynamically loaded and upstream source/object ancestry remain inherited.
The final endpoint's external-file binding remains separate.
