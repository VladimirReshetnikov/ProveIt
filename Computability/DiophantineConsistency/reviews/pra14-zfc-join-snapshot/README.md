# Draft coherent 14-equation/PRA refutation-bound join

This is a **frozen source snapshot and an unexecuted draft**, not a proof result. From the 847-source isolated 14-equation graph, the declared-import cone for `PRAWitnessZFCRefutationBound` adds 68 local sources; including the strict comparison and exact `PRACurrentZFCStrictChecks` adds five more. All 73 are frozen here. The first 71 source hashes match independently replayed strict-provider manifests. The two final `PRACurrentZFCStrict` source/check files are separately marked draft: the root reported an exploratory mixed-provider compilation and axiom check for these exact frozen source hashes; it is not a coherent-provider result. Four further direct Foundation objects and their available companions are pinned; each main object matches the strict refutation-bound manifest.

`run.py` reads and hashes the exact `replay.py` bytes and passes those bytes to a child process, which verifies their digest before executing them. The replay records the executed driver and launcher hashes and rechecks the persisted files at startup and in pre/post audits. The replay is designed to accept a completed isolated 14-equation parent only after its state reports PASS and its graph and package anchors match the frozen parent audit. It rejects overlapping/duplicate suffix modules, authenticates all 847 parent output objects, joined-object links, source snapshots and logs, verifies the recorded reuse manifests and origin states, checks original and package-mirror direct external object hashes and available companions, and builds the suffix in declared-import order using only `joined-lib:parent/package-lib` as `LEAN_PATH`. It records terminal failures and ordinary warning lines, and checks the final theorem's axioms. It has not been run because the parent remains incomplete.

Any eventual result remains a fixed source snapshot until the current workspace sources are separately compared after the build. The 14 parent reused objects only after a reconstructed source-declared transitive dependency audit; that reconstruction cannot rule out unrecorded mutation during their original compilation. Foundation and other external package transitive ancestry and dynamic imports remain inherited. An independent full suffix replay and direct examination of the final theorem are required before a completed PRA proof-existence claim.

A negative precondition test against the still-running parent is preserved as `negative-parent-precondition-state.json`: it recorded `FAILED`, zero compilation rows, and `parent is not PASS`. This tests the guard only; it is not a proof replay. The test covers only that precondition, not the rest of the replay driver.

A second negative precondition test through the authenticated launcher is preserved as `negative-authenticated-launch-state.json`. It recorded the executed driver and launcher hashes, zero compilation rows and `parent is not PASS`; it does not test the remaining replay path.

After the parent has finalized PASS and the driver has been reviewed, the frozen-snapshot replay command is:

```sh
python3 Computability/DiophantineConsistency/reviews/pra14-zfc-join-snapshot/run.py --parent /tmp/pra14-full-transitive-g3ull6n_
```

`declared-import-precheck.json` records a static topological check that each import declared by the 73 frozen suffix sources is already supplied by the 847-source parent graph, an earlier suffix module, or a pinned direct external object. It found no unaccounted or forward declared imports; it is not a Lean compilation or dynamic-import audit.
