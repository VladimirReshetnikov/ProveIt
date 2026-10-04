# Portable audit replay validation

Date: 4 October 2026. **PASS.** The replay adapter preserves the exact frozen independent checkers and redirects only their two historical data reads. No scientific source or checker byte was changed.

Adapter SHA256: `b902f194356b6ad803184889e764653732278b40aa3e99aa904970674d676fff`.

The independently authored packaging test performed two complete isolated replays:

1. A staged release with the writer's requested `science/`, `independent_audit/`, `universality/`, `dependencies/`, and `audit_replay/` layout
2. A tar archive extracted elsewhere, relocated to a renamed path containing spaces, with all bundle files read-only and all bundle directories nonwritable

Each run reproduced all three original receipts byte-for-byte:

- Exact source: `3befe9724413f4f7688068c542acf20669905def36c7e5192ca144cfd2c8dce9`
- Arithmetic: `15cc70d844d3b69f0568d5171e4916db89e1bdfe07980d537b443772ecb61589`
- Semantic: `4d7fe582a53138e1c7d42e0a1d2011bee6a58740c2e9827655072830ea1e86ff`

For both runs, the entire bundle's file bytes, sizes, modes, mtimes, directory modes/mtimes, and entry inventory remained unchanged. The original author science, independent audit, universality review, and inert Pell-wrapper inputs also remained unchanged through test setup and execution.

Negative controls separately changed a copied checker, source DAG, expected receipt, and Pell wrapper. Each was rejected by its exact input pin before any checker ran or output directory was created. In-bundle output, reused output, and a bundle symlink were rejected without bundle writes. Separate guard-sensitivity tests detected changes to content, mode, mtime, and entry inventory.

Every executed scientific checker was an unchanged copy of the independent auditor's source/arithmetic/semantic checker. No submitted builder, author checker, upstream program, saved schedule, or Lean was executed. The wrapper is specific to these inspected programs and does not claim to sandbox arbitrary malicious code.

Machine-readable results: `portability-receipt.json`. The original packaging run's detailed snapshots, worker traces, logs, and copied fixtures are retained in the development test-results directory and need not be included in the release.

A separate reviewer then independently reran the moved, read-only extracted bundle under isolated Python as UID 1000. That replay again produced all three frozen receipts exactly and independently verified all 49 bundle entries' bytes, sizes, modes, mtimes, and inventory. It confirmed that the replay receipt contains no historical `/workspace` absolute paths. No blocking findings were identified; see `independent-review-verification.json`.
