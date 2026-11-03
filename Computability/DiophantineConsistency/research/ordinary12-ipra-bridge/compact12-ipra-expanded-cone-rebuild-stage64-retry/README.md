# Expanded compact/iPRA rebuild: corrected stage 64

The previous stage 64 was rejected because Lean warned that `h` was an unused
argument in `simp [toAS, Enum254.fetch, h, hv]`. The checked workspace
correction changes that list to `simp [toAS, Enum254.fetch, hv]` and changes
nothing else in `BusyBeaver.ZFC.L2Root254`. The old and corrected source
snapshots have SHA-256 `20b2ef7733a0d85c5248ee598b5386f42ad46319a003488fb63bfacb7f737e9f`
and `fee84717177d6575f576ae3e09a3a034071f02422b7a5ef8d9d68e7822864d10`.

`repin.py` verifies both full source hashes, that exact single deletion, the
original cone hash and the rejected warning log and receipt. It changes only
the corrected source hash and size in a copy of the 425-module cone and adds
an explicit correction record; its `cone-repinned.json` SHA-256 is
`c9f4190a0d8807e5643f245a59ca53b23e52ca6c1dc1c1b74a5028651da049ec`.
The re-pin script has SHA-256
`20d81fe6f3ccbed53dacc1982976c1c8d74de9f2510489d3a80a97fa84d5ecb2`.
The captured `corrected-source.lean` is the current source snapshot, not a
separate assumption.

The retry runner checks the original baseline, requires all other source
pins and selected objects to match it, saves a separately re-pinned baseline,
and moves only the exact hash-recorded rejected object into a separate
quarantine before resuming. The original rejected evidence is not altered.
All first 63 output/log hashes and direct dependency and companion guards
were rechecked. Lean compiled the corrected stage in 2.054 seconds, exit 0,
without warnings or `sorryAx`; it produced the object SHA-256
`be781098ae7be6890210fb643f482c283258fecb825e0beb371f613d2df84ea1`.
The wrapper rechecked the full selected overlay, all 425 source pins,
rebuilt outputs and direct guards and exited 0: `completed: 64, total: 425`.
Source, dependency lists, logs, guards and receipt are in
`observations/batch-013/stage-0064/`. The exact runner has SHA-256
`2e58ed63b3947506bc7576fdeccd66d22b3c6f8ba611136a60f875b0db3abb80`,
and `observations/baseline-repinned.json` has SHA-256
`843271b7bf2ca668979bafe1a8f5509997567833091f25cbf91bda258e835995`.

This is an exploratory author prefix, not an iPRA endpoint, full coherent
build or independent replay. The compiler validates the corrected source in
this environment; source/object import-shape agreement still does not
establish historical origin. Package, dynamic and broader provider ancestry
remain unverified; 361 rebuild stages and the compact model-to-iPRA join
remain open. File and resource guards are point-in-time.
