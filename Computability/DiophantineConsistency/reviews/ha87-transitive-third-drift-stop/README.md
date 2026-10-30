# Third transitive full rebase stopped after validator drift

`/tmp/ha87-full-transitive-uqj917sj` was externally stopped at a safe child boundary after validator sources changed. Its terminal state is FAILED/KeyboardInterrupt on `ArithmeticDagControlPerm222`, with 129 reused rows and no newly verified output. Its state and 129 hashed transitive manifests are included. The exact validator before/after sources are in `../ha87-signed-validator-drift-stop/`; earlier source graphs, manifests and prefix ancestry are in `../ha87-transitive-second-drift-stop/` and predecessor packets.

The guard reconstructs original transitive environments from surviving origin objects and verified records, so it cannot rule out unrecorded mutation during original compilation. Dynamic imports and transitive package ancestry remain outside the audit. This stopped run is not proof evidence or an independent replay.
