# Six-edit candidate source snapshot

This source-only candidate freezes 1,099 regular Lean source files: 1,093
unchanged files copied from the previously checked snapshot and six edited files
captured from the workspace. The workspace matched the candidate at both the
initial and final scan. The 107-module source order comes from the separately
reviewed preliminary reverse-closure sizing and must still be independently
recomputed against the authenticated completed parent.

Lean's `--deps` parser agreed with the captured imports of all six changed files;
`lean-deps-receipt.json` (SHA-256
`da047c60ead0ca96b96bb1ba6db9c8128729af9616b5e8dccc3636a5d3383d2c`)
records the output. The earlier 1,099-file dependency check covers the 1,093
unchanged source hashes. The historical 258 peer only resolves dependency paths
for this parsing check; this does not make the snapshot an authenticated proof.

The parent-comparison gates, physical project-object environments, external
companion and absence checks, full successor closure, guarded replay and
independent comparison remain separate obligations. Any later workspace change
must be recorded by the replay and final comparator. The inherited author-only
848 ancestor and package-transitive/dynamic-import boundaries remain.

The source-capture process exited zero. Manifest SHA-256:
`a3a165cd4243d7df56c08a1a8c3a843c288e8736048682099e6966dda02d0e69`.
