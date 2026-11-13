# Independent review: bounded external Matrix preflight

**PASS for the retained partial inventory and stated scope.** The direct
`lean --deps` result records exit 0, the 22 new declared external modules,
the two deliberately supplied Matrix modules and implicit Init. All 24
explicit seeds select the package overlay; Init occurs twice at the same
path, with equal-hash root candidates. The 750 before/after path and
companion guards agree and still match at review time. This is direct path
resolution, not a combined import check.

The retained header observation records child exit 0, stable input hashes,
no resource stop and the captured log/result hashes; the separate terminal
observation records actual outer session 76951 exit 0. The 64 visited
modules include all 24 direct seeds at the same selected paths. Their
compiled main/private/server/IR import unions were rechecked against the
retained records; the 199 distinct frontier names are exactly the recorded
imports of visited names that were not visited. For each of the 22 new
seeds, recomputed reachability has no known Matrix route **and has a
nonempty unexpanded frontier**. The two Matrix nodes were supplied as
seeds. Thus no absence of a transitive route can be inferred.

The 1,920 recorded candidate/companion guards for the 64 visited names and
640 selected artifact entries were rehashed at review time. Among visited
main objects, only Init has multiple candidates and their hashes agree. The
20 historic Matrix path guards match the earlier captured import-order
failure evidence; the prior failure and this direct resolution test answer
different questions. The Python analysis reran with observed exit 0 and
byte-identical output. Independent [check.py](check.py) rechecks the frozen
receipts, identities, header-edge unions and partial reachability without Lean;
its observed exit-0 result is [result.json](result.json). We did not witness
the earlier direct or header process exits ourselves.

For an expanded or resumable traversal, treat an unexpanded frontier as
unknown and do not accept partial status as an absence proof. Revalidate
prior seeds, every saved edge and selected artifact against pinned tool,
policy and provider identities, and check all selected/alternate companions
and actual resolution. The existing supervisors are not sufficient as a
fail-closed lifecycle for a long new run: exceptions while monitoring can
escape before an owned process group is terminated and reaped, and leader
exit alone does not prove its descendants are gone. Use a separately
reviewed owned-session supervisor with exception-safe cleanup, actual outer
exit capture and explicit resource-stop receipts. Even a complete static
header traversal would not prove source-to-object provenance, dynamic loads,
absence of between-observation changes, or successful combined imports.
No Lean replay, new project build or iPRA theorem was produced here.

Frozen source README SHA-256
`c85992226d10e79afa9bd9fdec82b0e6a2d75e7292c1e3692525c8e190ad39ef`.
Independent checker SHA-256
`f1854bc5dddff90de3d9bd8b40948766b07bfa68f7cf2fddaed5bc28e80bbc80`;
result SHA-256
`25a9ce4eef0f5e656e8715621204e3a099e7055d3675030c4e130954b773f405`.
Frozen receipt hashes are pinned within the checker.
