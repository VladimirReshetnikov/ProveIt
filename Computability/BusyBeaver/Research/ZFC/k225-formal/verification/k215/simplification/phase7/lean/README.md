# Lean phase 7: pointwise implication proof

The exact 215-state endpoint passed its complete 187-module project closure, with Lean's shipped `Init` boundary. This checkpoint freshly compiled 2 modules and reused 185 immutable phase 6 providers after source, import, direct dependency, object and log checks. It is an incremental checkpoint, not a fresh compilation of all 187 modules.

Only `DomRho8.lean` and its producer changed. The shorter proof lifts a proved implication pointwise, replacing the longer deduction-based final argument. The unused public helper `distribution` was removed after a recorded consumer census; the endpoint statements and exact machine remain unchanged. The 186 other primary source files and all imports are identical to phase 6. Seven modules are potentially affected by the changed source, but the fresh count above follows actual object hashes.

Both unchanged typed clients passed: `EndpointAudit215` contributes two named reports and `K215Audit` eight. Their reports use only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. Audit logs have no warnings; selected project logs contain 22 linter warnings. The separate live review rehashed all 187 current providers and all 187 phase 6 providers and logs after checking both audit objects.

[result.json](result.json), [live-review.json](live-review.json) and [index.json](index.json) bind `execution.tar.gz`. It retains the complete current source snapshots and dependency ledger, all fresh attempts and audit records, the two exact adopted files, isolated proof and generation history, source peers and the original driver. The isolated check's five reports and the generator's three positive/four rejection controls remain separate from the full endpoint check. Original prospective status text is preserved rather than rewritten. No compiled objects are archived.

The [phase 6 packet](../../phase6/lean/README.md) is required locally. [basis-reference.json](basis-reference.json) pins its exact repository-relative archive, index, result, live review and validator files. Reused logs are referenced explicitly through `execution/reused-log-origins.json`; they are not duplicated. The saved reader checks the pinned local phase 6 validator chain, including its existing phase 5 reference. No archived source is executed and no predecessor archive is copied into this packet.

Run the saved reader from this directory with an unused output path:

```sh
python3 -B review_saved.py --output /tmp/k215-phase7-saved-review.json
```

A relocated packet needs `--basis-repo /path/to/Proofs`. Optional `--repo /path/to/Proofs` also checks current source, producer and machine bytes. Historical saved review does not inspect live objects or invoke Lean. The separately retained live checker performs that read-only inspection while the original caches exist. The [maintained fresh build](../../../lean/README.md) remains the complete rebuild route.
