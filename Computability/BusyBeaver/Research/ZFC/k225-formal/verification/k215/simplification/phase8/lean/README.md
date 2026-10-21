# Lean phase 8: shared implication and seed arguments

The exact 215-state endpoint passed its 188-module project closure, with Lean's shipped `Init` boundary. This incremental checkpoint freshly compiled 8 modules and reused 180 immutable phase 7 providers after checking source, imports, direct dependency objects and logs. The fresh count follows actual object hashes.

The implication argument now lives in the representation-independent `DominatedImplication` core; the shorter `DomRho8` adapter instantiates it for the native code. Shared `BundleSemantics` factors the forward and reverse seed arguments. Four Lean sources, two producers and three text templates are registered. The other 184 primary sources, exact machine and endpoint statements are unchanged. The primary closure gains the one new implication module.

Both unchanged typed clients passed: `EndpointAudit215` contributes two named reports and `K215Audit` eight. Reports use only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. Audit logs have no warnings; selected project logs contain 22 linter warnings. The independent live review rehashed all 188 current and 187 basis providers and logs after checking both audit objects.

[result.json](result.json), [live-review.json](live-review.json) and [index.json](index.json) bind `execution.tar.gz`. The archive retains all current source snapshots and dependency records, fresh attempts and audit logs, nine registered files, exact raw producer inputs, isolated checks, source peers and original preparation failures. Root's isolated check of four modules and two clients produced 17 reports. Drop's separately attributed producer controls comprise five positive and 13 rejection cases. These remain distinct from the full endpoint check. Prospective statuses are retained as written. No compiled objects are archived.

The exact [phase 7 packet](../../phase7/lean/README.md) is required locally. [basis-reference.json](basis-reference.json) pins its repository-relative archive, index, result, live review and validators. The reader uses only pinned local validators and resolves predecessor log references in memory. No archived source is executed; earlier archives and reused logs are not copied into this packet.

Run the saved reader with an unused output path:

```sh
python3 -B review_saved.py --output /tmp/k215-phase8-saved-review.json
```

A relocated packet needs `--basis-repo /path/to/Proofs`. Optional `--repo /path/to/Proofs` also checks current source, producer, template and machine bytes. Saved review does not inspect live objects or invoke Lean. The retained live reviewer checks those objects while the original caches exist. The [maintained build](../../../lean/README.md) remains the full fresh rebuild route. Legacy continuity is recorded separately.
