# Fourth transitive full rebase stopped after source drift

`/tmp/ha87-full-transitive-ypddlu9w` was externally stopped at a safe child boundary after four merged project sources changed. Its terminal state is FAILED/KeyboardInterrupt on `ArithmeticDagControlPerm222`, with 129 reused rows and no newly verified output. The state and 129 hashed transitive manifests are included. Before/after source deltas and the updated graph are in `../ha87-scaled-import-refresh/`; earlier prefix ancestry is in `../ha87-transitive-third-drift-stop/` and predecessor packets.

The historical reuse guard reconstructs original transitive environments from surviving origin objects and records; it cannot rule out unrecorded mutation during original compilation. Dynamic imports and transitive package ancestry remain outside this audit. This stopped run is not proof evidence or an independent replay.
