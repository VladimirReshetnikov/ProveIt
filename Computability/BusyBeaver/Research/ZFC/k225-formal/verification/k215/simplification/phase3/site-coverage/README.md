# Compose the checked site blocks directly

The coverage facade shrinks from 107,243 to 14,916 bytes. A single nested proof
composes the same 105 kernel-checked blocks with `allSites_join`, replacing 104
named intermediate joins and their repeated Boolean paths. The nine batch files,
all 4,751 leaf checks, and the public `all_sites` and `covered` statements stay
unchanged. No external Lean source uses the removed intermediate names.

The [exact candidate](KSites215.lean) passed in 1.066 seconds with zero warnings.
The [typed client](Audit.lean) checks both public theorem types; its
[axiom reports](api.log) match the original facade exactly: `propext` for
`all_sites`, and `propext`, `Quot.sound` for `covered`.

The producer change is retained in the [execution archive](execution.tar.gz).
The [regeneration control](regeneration.json) reproduces the checked bytes and
all nine unchanged batch files. A separate [preparation control](prepare-control.json)
keeps both maintained generators intact and reproduces the other five preparation
outputs exactly. The maintained [site generator](../../../../../generate_sites215_lean.py) receives this
change when the candidate is adopted after the frozen phase2 check.

An [independent review](independent-review.json) expands the original named
joins and checks that the new proof uses the identical tree, with every block
appearing exactly once. It also checks the public theorem statements, saved
kernel records, and generator/preparation changes.

The [result](result.json), [source record](source-check.json),
[client record](api-check.json), and [archive index](execution-index.json) retain
the execution boundaries. This isolated facade check does not by itself record
a rebuild of the combined current endpoint.
