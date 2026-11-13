# Independent v6 runner preflight

The reviewed `run-v6.py` has SHA-256
`0c1d2e7302ff5a6d8f7c3ab3e5957401dc7efae7488264e47257db419acb5a2c`.
The v6 changes retain the previously reviewed guarded provider selection,
actual project-header traversal, object/companion snapshots, allowed-axiom
checks, and completion receipt binding. They pin the separately audited
QSchema source repair and allow the initial rebuild receipt directory.

The retained read-only check invokes v6's manifest, companion, and producer
receipt validators without launching Lean. All 425 candidate modules passed,
including original rebuild stages 1–5, the exact successful stage-419 QSchema
receipt, and the exact successful stage-425 completion receipt. A separate
check normalizes the repaired QSchema cone entry back to its old source hash
and size and verifies all other cone fields are unchanged. The observation
exited zero with empty stderr.

This preflight is not the join: subsequent actual Lean compilation, full
selected-project header scans, and the runner's other fail-closed checks still
have to succeed. Package-transitive and dynamic ancestry remain outside the
runner's claimed scope.
