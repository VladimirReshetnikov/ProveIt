# Row encoding and operating-row exclusion: independent peer review

Date: 2026-10-26. Reviewer: complemented47_review. Author of the four reviewed sources: ROOT. Result: **PASS; no mathematical, premise, or source-binding finding.** No source changes were requested or made.

## Scope and independence

I read all 76+41 lines of `WangTiles942RowEncoding` and its checks, and all 71+39 lines of `WangTiles942OperatingRow` and its checks. I read their author receipt for provenance, then assessed the proofs and declarations directly. I also read the complete `WangTiles942StripGeometry`, `WangTiles942ResetRows`, and `WangTiles942InputLanguage` sources, and inspected the exact `InitialStrip` fields and marked-plane time/address interfaces used here.

I authored dependencies `DecimalMachineInitialization`, `WangMachineEncoding`, and the earlier literal table/cache modules. I also authored the later `WangTiles942HeadBounds`, which consumes OperatingRow. This is an independent review of ROOT's two modules and their composition, not a claim of independent authorship or a new independent proof of my own dependencies. The reset propagation theorem in `WangTiles942ResetRows` is another agent's prior work. The present fresh replay reuses already available dependency objects; it is not a fresh build of the entire import closure.

## Frozen sources

Paths in this table are under `Lean/DiophantineConsistency/`.

| Source | SHA-256 |
| --- | --- |
| `WangTiles942RowEncoding.lean` | `d9c24628856b55b6e91b843208539982810d84fbb6f2b5882382b61f4a3cb9df` |
| `WangTiles942RowEncodingChecks.lean` | `bd4ffcc7b65d3200f610168ec69108ffc75df19e18d17113e85aab12da7ed6c5` |
| `WangTiles942OperatingRow.lean` | `f92a15534d5bfdfedb124aef9dac8cc2660b4eacd78562be25066ce66c02e443` |
| `WangTiles942OperatingRowChecks.lean` | `6534650b8a59d225db8aa0fd64067fcf795560c33942e64dd33febaf3f4cae88` |

Dependency bindings checked at review time:

| Source | SHA-256 |
| --- | --- |
| `WangMachineEncoding.lean` | `0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e` |
| `DecimalMachineInitialization.lean` | `748587f903a4a1cc0d0c475ebc0ba9628887eaff0584e6d3a7944f4115b6b82f` |
| `WangTiles942StripGeometry.lean` | `2439e3e5bd3b9f4eeea38013e4a2e237444626cc5864b0244463be8a88ce4e7a` |
| `WangTiles942InitialStrip.lean` | `b20872f398fc330069ba8eec137d295bc6f6418b6c215a53afcff6334128a100` |
| `WangTiles942Periodic.lean` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |
| `WangTiles942ResetRows.lean` | `c12f1209b1a90e967859a10e989b7fde9ae32bbcf8b6245f99ca267adcdf7513` |
| `WangTiles942ResetHorizontal.lean` | `1cba7e914d13a2d6053b5d35b7b308f08093ae99d36c8963952f0de05f663ebc` |
| `WangTiles942InputLanguage.lean` | `a28c66e285b3fc652392bc9d58c04135a4fef1f11b4a7e4378a0e02a4416307c` |
| `WangTiles942Boundary.lean` | `efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c` |

## Mathematical audit

`RowEncodes` contains exactly two strict head bounds and the actual north-color equality at every integer position in the open interval. It contains no assertion about exterior tape cells, no future row, no absence of finish tiles, no run extraction, and no transition equation. Its local projections correctly separate plain colors 0/1 from head colors 2..433, including the halted head colors.

`initialized_row` uses `InitialStrip.left_pos` and `right_min` to put head position 1 strictly between the walls. The existing `initial_south` formula is exactly 1 at position 0, 4 at position 1, and 0 elsewhere inside. Actual vertical matching transfers that formula to north colors at time 1; `WangMachineEncoding.initialized_color` gives the same function for the proven actual post-first-step configuration. `marked_initialized_strip` derives the persistent strip from `MarkedWord`, uses the actual plane's temporal equation at time 0, and rewrites by `DecimalMachineInitialization.run_one`. The machine clock is therefore exactly 1, with no blank-row or independently seeded-run substitution. The marked-word assumption supplies only its actual tile word, origin Start and two matching conditions.

For OperatingRow, `symbol cfg x` is precisely the actual tape Boolean converted to a `Fin 2` value. At the interior operating head, the encoded input equals `headColor q bit` with `q < 215`; `north_operating_iff_transition` forces the unique actual transition row at index `2*q+bit`. Its South value is the actual cached action's Boolean write bit, so the bound at most 1 needs no next-row or target-state assumption.

`no_south438` starts with one hypothetical interior South438 edge. The exact time equation produces a North438 reset at that position in the following row. `strip_finish_and_reset_of_south438` propagates the reset horizontally across the connected open interval, using the persistent interior's absence of seams at that following time. Time matching then gives South438 at every original-row position, including the already interior operating head. This contradicts its forced Boolean South value. The call supplies only allowedness, actual horizontal/time matching, the seam-free interior, and the hypothetical single edge; it does not supply a uniform finish/reset row or any no-finish premise. `no_finish` correctly follows from the actual `FinishTile.south` projection.

The operating-state restriction is material: the focused checks retain genuinely allowed plain finish tiles and a genuinely allowed halted-head finish. The proof does not incorrectly exclude either local form in general. The row checks also retain the North435 obstruction for every encoded interior position, even when the configuration is halted.

## Isolated fresh replay

I created `/tmp/wang-row-operating-peer-s6oos2p4/objects/DiophantineConsistency`, linked unchanged dependency artifacts into it, and excluded all four reviewed module stems. I prepended that object root to the exact `lake env printenv LEAN_PATH` result. Then I compiled, in order, RowEncoding, its checks, OperatingRow, and its checks with the actual Lean 4.32.0 binary and `-M 6000 -j 1 -o <isolated-object> <absolute-source>`. Thus each checks file imported its freshly generated main, and OperatingRow imported the freshly generated RowEncoding. No shared object was overwritten.

All four first attempts exited 0, in 2.904, 2.837, 2.861, and 2.751 seconds respectively. Both main logs are empty and both check logs contain only the expected axiom reports. All ten reports use only `propext`, `Classical.choice`, and `Quot.sound`. Both fresh main objects are byte-identical to the preexisting shared main objects. The shared check objects were absent before and remained absent afterward. All reviewed source hashes and shared objects were unchanged.

Exact commands, environment, outputs, before/after hashes and timing are in `/tmp/wang-row-operating-peer-s6oos2p4/receipt.json`, SHA-256 `78e3fd66ed7b3e390e0f097b70ee7f9e117767b5f2519d82f1c1cd442ed61148`. The RowEncoding check log has SHA-256 `0fe9dcfd6c4aa0593eb703753fbf4cf56c993987015b9b6422e88455d5ac57b6`; OperatingRow check log has `f7d7f54dd7fa32219dc0622d846c6c0fd68e4040af6af3e571387359121414d0`.

No proof gap or unreported added premise was found in this scope. Successor-row machine semantics, eventual halting, the reverse construction, and the complete equation/consistency equivalence are separate obligations; this review does not treat them as established by these two packets.
