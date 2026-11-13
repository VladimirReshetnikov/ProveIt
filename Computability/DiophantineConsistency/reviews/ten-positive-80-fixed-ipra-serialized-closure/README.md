# Fixed symbolic 80 iPRA selected import closure

`scan.py` traverses the serialized `.olean` imports of the accepted
`Direct80SymbolicFixedIPRA` object using the exact recorded fixed-client
search path, with its output root first. The scan found 1,765 selected project
modules and 80 selected outside names. Of the project modules, 1,608 match
objects from the pinned, previously captured 90 iPRA post-join inventory;
their captured direct headers were reused only after checking the currently
first-resolved object hashes. The other 157 actual object headers were read
in 19 guarded Lean batches. Repeated or missing header records are rejected.
The scanner checked every project-path candidate for each selected project
ancestor and found zero candidates with different object hashes. It checked
the root and fixed input hashes before and after, and rechecked selected
objects at the end.

`audit.py` independently reconstructs the transitive graph from those
captured headers, recomputes first-resolved paths and all project candidates,
rehashes each recorded candidate and outside selection, and compares the
recorded companion presence and hashes for the 1,608 reused project objects
with the 90 inventory. The 1,608 present matching companion entries are the
`.olean` objects; the 90 inventory records no other present companions for
these selections. Its successful read-only result is
`observations/audit02.stdout`, SHA-256
`03487963894d40789cdc0a12e7342c19e3cb665c6e9d5c284c9847c22652a2c0`.
The scan result is `observations/attempt01/result.json`, SHA-256
`d65d7c776eb23425f9e2a290d8c3fdeebc011920619241290fdee85bc4ae68a9`.
It records every selected path/hash, all project candidates, fresh headers,
outside names, preflight and postflight samples, and the exact search roots.

`producer_audit.py` found retained successful single-object producer receipts
for 126 of the 157 fresh-header objects. Re-resolving their recorded producer
search paths now gives the same direct-import hashes as the final closure.
Twenty-five of those receipts explicitly pin every source-direct import; each
of those pins matches the final selection. The remaining 101 matched receipts
do not provide that explicit direct-pin evidence, and 31 fresh objects were
not matched by this receipt search. This comparison therefore does not prove
that unpinned dependency bytes were the same at producer time. Its detailed
result is `observations/producer-audit01.json`, SHA-256
`2686e7522cec011ab1cf4d5661662b57fadd9613a2bbe87bd46ad10c79ef8b6e`.

Each header batch required at least 8 GiB available and fewer than two Lean
processes before launching; those per-batch samples were not persisted. The
stored preflight and postflight are point samples and do not establish the
minimum available memory throughout the scan. The author process exited 0;
no separate process-terminal receipt was recorded. `audit.py` can be rerun
with `python3 -I -S -B audit.py` while the pinned temporary providers remain.

This is an audit of the selected `.olean` closure and the stated overlaps,
not a fresh compilation or authentication of all historical source-to-object
ancestry. New-module companion files and producer-time dependency paths have
not been completely reconciled here. Outside objects are checked as selected
files, but their transitive imports, companion files, dynamic loading and
package provenance remain outside the result. The audit does not bind the
Lean graph to an external PDF or JSON, and the retained external 80 K0 still
differs from the symbolic coefficient used by the fixed iPRA client.
