# Eight-module compiled-header measurement

The first attempt stopped before traversal because it treated an absent Lake
search root as an error; its [failure record](initial-attempt.json) is retained.
The reviewed implementation records and guards that absent root instead.

The [bounded receipt](partial-receipt.json) and [actual terminal observation](partial-observation.json)
record an eight-module traversal from `Foundation.Vorspiel.IsEmpty` under the
audited Foundation build's recorded [Lake search path](lake-path-policy.json).
It ended with **56 pending modules**, so it is not a complete closure. The
process used idle I/O priority, `nice` 19 and a 2 MiB/s limit on explicit hash
reads; it hashed 4,215,296 bytes across baseline and final checks. Those are
bytes passed through SHA-256, not a measurement of physical disk traffic or
Lean's memory-mapped reads.

The receipt records compiled header dependencies and point-in-time object
identities only. It establishes neither source-to-object provenance nor a
trace of actual dynamic/runtime loads, and it cannot exclude transient
mutation. No broader survey has been started while the project proof replay is
running. Independent reader review is recorded separately.
