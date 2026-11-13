# Shifted Pell sandwich rebuilds

The generic `PellScaledSandwich.lean` and `PellScaledUpper.lean` have been
rebuilt against the arithmetic-only `PellVariableGrowth` provider. Their
theorem bodies match the corresponding earlier research sources; explicit
arithmetic imports were added so that the needed namespaces are visible
without importing the old 80 graph. They establish conditional lower and
upper inequalities at shifted Pell parameters. Neither proves a trace75
graph conclusion or population bound on its own.

The accepted lower build is `run-sandwichgeneric-v2.py`,
`observations/sandwichgeneric-attempt02/`, object
`/tmp/pell-scaled-generic-5jabps73/PellScaledSandwich.olean`, SHA-256
`0c172072f014a60e7ba1548cf2762232d2c86c3e1a95380e76d46879902feea6`.
The unchanged-import first attempt is retained; it failed on namespaces
previously supplied by the old graph import. The accepted upper build is
`run-uppergeneric.py`, `observations/uppergeneric-attempt01/`, object
`/tmp/pell-upper-generic-g4yjs_ug/PellScaledUpper.olean`, SHA-256
`ffaea0b89a05df089d988423ecffac9614131bd4f3e660863c91f03487e6b0f9`.
Both accepted Lean checks returned 0 without warnings. Direct objects and
the first-resolved historical `ModelRatioBounds` are pinned; its known
producer-time drift and full transitive/package provenance remain open.
