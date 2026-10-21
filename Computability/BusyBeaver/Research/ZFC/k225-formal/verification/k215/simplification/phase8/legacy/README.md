# Phase 8 legacy continuity and fresh typed audit

All 15 retained legacy proof objects remain reusable with the 188-module phase-eight primary closure: **203 selected providers, zero legacy recompilations**. The changed `DomRho8` proof and new `DominatedImplication` core occur in the unchanged five-client audit's 46-module transitive closure. `LegacyAudit` was therefore compiled again, with five named standard-axiom reports and zero warnings.

Every selected source/import/dependency/object/log binding and the fresh audit object was rehashed after execution. This is incremental continuity with a fresh typed audit, not a fresh 203-module build. The [primary packet](../lean/README.md) and [phase-seven legacy packet](../../phase7/legacy/README.md) retain their distinct histories.

`execution.tar.gz` preserves the executed driver, preparation and correction history, metadata controls, driver peer, selected ledgers, exact audit source/command/raw log/receipt, root observations, and publication helpers. It contains no compiled objects or duplicate ancestor payloads. `references.json` binds the two immediate predecessor packets. The saved reader follows their pinned references to the original source/log records, treats archives only as data, and never invokes archived scripts or proof tools.

```sh
python3 -B review_saved.py --basis-repo /absolute/path/to/Proofs \
  --output /tmp/phase8-legacy-saved-review.json
```

Add `--repo /absolute/path/to/Proofs` to check the current 203 source files and nine registered source/producer/template files. Default verification checks the historical archived checkpoint. Live object hashes are recorded evidence in `live-review.json`; the saved reader does not claim to inspect historical object files.
