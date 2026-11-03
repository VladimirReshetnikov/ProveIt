# Independent review: 28 graph-support overlay objects

PASS for the point-in-time candidate triage in `research/trace75-graph-support-28-triage/`. We independently reconstructed the 28-object subset from the pinned 141-, 19- and ten-runner inventories and final selected realpaths; rehashed every selected object; and checked the captured headers. For 27 objects, the current same-name overlay source matches exactly one prototype workspace source byte-for-byte and its explicit imports match the selected captured header. `DiophantineConsistency.ArithmeticPackingBlocks` has no same-name overlay source; the current canonical workspace candidate has matching declared imports but is not identified as its producer source.

Twenty-two objects have one or more same-name overlay logs, and seven prototype directories contain JSON candidates mentioning both the observed source hash and selected object hash; none of these candidate JSONs contains the exact selected output realpath. We independently enumerated and rehashed those files. Matching filenames, source bytes, headers or textual hash mentions do not establish that these sources or logs produced the selected objects, nor authenticate historical direct imports.

No compile commands, producer-time source/object linkage, complete upstream source ancestry, package/dynamic inputs or external equation-file binding are established. No Lean replay was performed.

Checker SHA `2efe676d2fd92626cb878628f6cf948547fcce2c64b282f3effa339856a29fdf`, terminal SHA `6b2dcfae50c3ccee1f60657691cd809df9d15319508c16a06a83e476f95dcb5a`, stdout SHA `a1f701226ce2c5c1f9eef7b627f4d6ce6aa494bc4689c846d8617f172d750570`. Our independent checker and output are alongside.
