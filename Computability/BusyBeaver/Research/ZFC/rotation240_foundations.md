# Exact 240-state table and fast lookup checked in Lean

Lean checks the exact published 480-action table and proves that a balanced
transition lookup defines the same machine. The two source/audit pairs pass
nine named theorem probes and eleven typed callers, with zero warnings.

[TableRotation240](../../Lean/BusyBeaver/ZFC/TableRotation240.lean) supplies the
240-state table, inherited-label inverse, canonical start 0 and dispatcher 84.
Its only halting action is inherited state 77 reading 1, writing 1 and moving
right. Seven probes and seven callers pass; source elaboration took 9.255
seconds and the audit 0.246 seconds.

[FastTableRotation240](../../Lean/BusyBeaver/ZFC/FastTableRotation240.lean)
proves equality for every state and input bit, then equality of the entire
machine. Two probes and four callers pass, including run equality from any
configuration at any time. Source elaboration took 5.059 seconds and the
audit 0.237 seconds. Transition equality uses no axioms; whole-machine
equality uses `Quot.sound`. The table audit has two empty axiom sets and five
containing only `propext`.

The [table audit](table_rotation240_audit.lean),
[fast audit](fast_table_rotation240_audit.lean),
[table result](results/table-rotation240-verification.json) and
[fast result](results/fast-table-rotation240-verification.json) retain the
actual checked sources and results. Both checks use one thread, 4,096 MiB,
default proof limits and a shared 120-second source-plus-audit deadline.
They capture each fresh object before its audit and check input and provider
identities afterward. No dependency build, download or compiler-version query
is performed. The exact input tables retain the attribution recorded in the
[construction](candidate-rotation240/README.md).

The [publication record](rotation240-foundations-formal/publication.json) and
[compressed history](rotation240-foundations-formal/history.json.gz) preserve
the original generators, guards, preparation, raw logs, independent reviews
and the corrected headerless-input gate. Compiled objects and symlinked caches
are excluded. The maintained [table wrapper](check_table_rotation240.py) and
[fast wrapper](check_fast_table_rotation240.py) change only path defaults;
both pass `--prepare-only` against the retained historical provider cache.
These wrappers do not yet supply a clean-checkout dependency build.

These results identify the exact machine and make later execution proofs
more efficient. Binary runtime coverage, complete blank initialization,
the final consistency equivalence and its internal PA proof remain open.
