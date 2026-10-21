# Lean phase-three proof simplification

The 215-state endpoint passed with the complete 185-module project closure and only Lean's shipped `Init` boundary. This checkpoint freshly compiled 9 affected modules and reused 176 phase-two objects after checking their source, direct dependencies, object and saved-log hashes. It is an incremental kernel check of the complete closure, not a new fresh compilation of every module.

Both typed endpoint audit clients passed: `EndpointAudit215` produced two axiom reports and `K215Audit` eight. Every report contains only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero audit warnings. The selected source-module logs contain 31 linter warnings. The independent live review checked all 185 private objects and the immutable 185-object phase-two basis after checking the audit objects and reports.

[result.json](result.json) and [live-review.json](live-review.json) record the final boundary. [index.json](index.json) binds each member of `execution.tar.gz`: all 185 source snapshots; exact source/import/object/dependency ledgers; every fresh attempt's source, command, raw log and record; both typed clients; original runners; and the read-only reviewers. Failed historical attempts, if present, remain separate from the selected PASS ledger. Compiled objects are excluded.

The archive's `basis/` directory preserves the original phase-two inventory, completed ledger, owner, result, raw selected logs and live review, together with the retained phase-one origin records. These are copied bytes, not rewritten histories. The copied toolchain file retains its original 204-module description; only its compiler and shipped-core identities are inherited here. The phase-three inventory and result establish the current 185-module scope. [Phase-two evidence](../../phase2/lean/README.md) and [phase-one evidence](../../lean/README.md) remain the predecessor checkpoints.

Run the portable saved-evidence check with:

```sh
python3 review_saved.py --output /tmp/k215-phase3-saved-review.json
```

This checks the archive without executing Lean or any archived runner. It verifies all 185 source snapshots and imports, exact dependency/object hash records, inherited log bindings, fresh compiler commands and the two audit reports. Optional `--repo /path/to/Proofs` additionally requires every checkpoint source and unique provider path to remain current. Neither mode rechecks live compiled objects; that claim belongs to the separately saved live review. The [maintained fresh-build driver](../../../lean/README.md) provides the independent full rebuild route. Original executed scripts retain their historical scratch paths.

The portable [saved review](saved-review.json) passed against this archive. The [helper source peer](helper-source-review.json) independently reviewed the live/saved checkers and publisher; its prospective status remains unchanged. [Synthetic metadata controls](metadata-controls/README.md) check the evidence logic only and make no compiler claim.
