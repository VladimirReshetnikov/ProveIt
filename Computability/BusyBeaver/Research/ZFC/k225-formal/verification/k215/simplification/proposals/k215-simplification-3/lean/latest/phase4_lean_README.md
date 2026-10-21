# Lean phase-four proof simplification

The 215-state endpoint passed with the complete 185-module project closure and only Lean's shipped `Init` boundary. This checkpoint freshly compiled 10 affected modules and reused 175 phase-three objects after checking their source, direct dependencies, object and saved-log hashes. It is an incremental kernel check of the complete closure, not a new fresh compilation of every module.

Both typed endpoint audit clients passed: `EndpointAudit215` produced two axiom reports and `K215Audit` eight. Every report contains only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero audit warnings. The selected source-module logs contain 31 linter warnings. The independent live review checked all 185 private objects and the immutable 185-object phase-three basis after checking the audit objects and reports.

[result.json](result.json) and [live-review.json](live-review.json) record the final boundary. [index.json](index.json) binds each member of `execution.tar.gz`: all 185 source snapshots; exact source/import/object/dependency ledgers; every fresh attempt's source, command, raw log and record; both typed clients; original runners; and the read-only reviewers. Failed historical attempts, if present, remain separate from the selected PASS ledger. Compiled objects are excluded.

The archive's `basis/` directory preserves the original phase-three inventory, completed ledger, owner, result, raw selected logs and live review. `basis-checkpoint/` retains the exact phase-three archive, index, summary and live receipt, including all earlier provenance. The saved reviewer checks every nested member and runs the unchanged reviewed phase-three validator as a trusted local sibling, never executing archived code. Both layers exclude compiled objects. The copied toolchain file retains its original 204-module description; only its compiler and shipped-core identities are inherited here. The phase-four inventory establishes the current 185-module scope. [Phase-three evidence](../../phase3/lean/README.md) remains the predecessor checkpoint.

Run the portable saved-evidence check with:

```sh
python3 review_saved.py --output /tmp/k215-phase4-saved-review.json
```

This checks the archive without executing Lean or any archived runner. It verifies all 185 source snapshots and imports, exact dependency/object hash records, inherited log bindings, fresh compiler commands and the two audit reports. Optional `--repo /path/to/Proofs` additionally requires every checkpoint source and unique provider path to remain current. Neither mode rechecks live compiled objects; that claim belongs to the separately saved live review. The [maintained fresh-build driver](../../../lean/README.md) provides the independent full rebuild route. Original executed scripts retain their historical scratch paths.

The independent [metadata controls](metadata-controls/README.md) retain their source and all 21 rejection results. A separate [root live review](root-live-review.json) rehashed the current and predecessor object sets without invoking a compiler.
