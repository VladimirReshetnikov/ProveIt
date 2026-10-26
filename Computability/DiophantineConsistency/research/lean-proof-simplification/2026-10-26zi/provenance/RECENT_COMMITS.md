# Recent commits and authenticated source snapshot

## Scope and pinned baseline

This fourth review inspects [`e652d21c413d`](https://github.com/VladimirReshetnikov/ProveIt/commit/e652d21c413de59e4821f6e8e9b6a3a077bf5bfe) (26 October 2026, 17:28:55 UTC), relative to the preceding review's [`22e020937caa`](https://github.com/VladimirReshetnikov/ProveIt/commit/22e020937caa81d0cb72a4f63071d6c0bcc1eba9). The GitHub compare metadata reports **33 commits ahead, zero behind**. Walking the returned commit graph and subtracting the previous pin's ancestors independently produces exactly those 33 commits. This matters because two newly incorporated proposal commits have timestamps earlier than the previous pin; simply stopping a date-ordered list at that pin would miss them.

The 33 commits comprise 12 merges, 8 proposal-intake commits, 4 adopted proof-refactor commits, 5 new-construction commits, and 4 verification/review commits. Proposal intake is not proof adoption. Repository review records describe upstream Lean checks; those checks were **not rerun in this review**.

## Authoritative active-source delta

Complete, untruncated Git trees contain **608 old and 637 current active Lean files**, with **29 additions, 10 modifications and no deletions**. The 29 additions consist of 14 new construction modules, their 14 companion check modules, and the shared `FreeCarrierCoordinates` helper. The 10 modifications comprise nine existing proof modules plus the umbrella import file.

The GitHub compare wrapper returned exactly **300 repository file records**. That list is capped, so it was not treated as a complete repository change inventory. Instead, the active Lean subtree was compared by path and Git blob SHA from its complete old/current trees. All 39 authoritative active-source changes happen to appear in the capped compare list; there are no missing active entries, unexpected entries, or status disagreements. The absence of an active-source discrepancy does not remove the cap for the rest of the repository.

The current active subtree is bound to tree `eaba62353b478bf4c481ac837f7f15f2fe0fe602`. `active_tree_delta.json`, `active_delta_crosscheck.json`, the two Lean tree manifests and source-level diffs make this comparison replayable offline.

## Observed adoptions: exclude these from new proposals

The following four source refactors are already present at the current pin. Net reductions were independently recomputed from authenticated complete-file bytes, including the cost of shared helpers—not merely copied from commit messages.

| Commit | Adopted simplification | Net Lean lines removed |
|---|---|---:|
| [`79bc166a51`](https://github.com/VladimirReshetnikov/ProveIt/commit/79bc166a515bd0f07cac826ad1a1bc1e486c88d2) | Checked-label generated Steps | 1,646 |
| [`32b108f214`](https://github.com/VladimirReshetnikov/ProveIt/commit/32b108f2146dc7d6ce1e0c55af9a541a0204a190) | Shared nine-coordinate transport | 26 |
| [`2effe6f291`](https://github.com/VladimirReshetnikov/ProveIt/commit/2effe6f2916bbbe6308b2b2ea674369a490901d9) | Radix, convolution, selector and carry cleanup | 22 |
| [`8ca6455829`](https://github.com/VladimirReshetnikov/ProveIt/commit/8ca645582907208196b539bf72a8022db4975b67) | Shared ordinary/doubled Pell ratio estimate | 77 |
| **Total** | **Including every introduced helper** | **1,771** |

The Pell total includes the lower-level `HilbertTenthProblem/.../PellRatio90.lean` module: it grows from 472 to 478 lines while `NativeHalfBinomial` shrinks from 244 to 161. Omitting that dependency would overstate the saving by six lines. The generated Steps group retains the shared generator as its maintained source; its Python-file changes are not included in the Lean-line metric. These are source-size reductions, not measured compilation speedups.

The nine modified proof modules remove 1,816 lines; the new coordinate helper costs 39, so the active-subtree refactors save 1,777 lines. The separate lower-level Pell helper costs six more, producing the 1,771 total above. New construction/check modules add 2,836 lines and the umbrella adds 14 imports; consequently the full active subtree grows by 1,073 lines. This growth is new functionality, not a contradiction of the measured refactor savings.

**Two baselines are deliberately distinct.** The observed baseline records what is actually in the pinned source. For novelty screening, the user's stronger instruction takes precedence: every idea in `research/lean-proof-simplification` and `docs/incoming` is treated as already applied, even if it has no maintained-source adoption yet. Repository `ADOPTION.md` or a successful archived compilation does not make a prior idea eligible to propose again.

## Newly added source families worth inspecting

- `CurrentSoundness2011` and its checks: current literal equation soundness.
- `CurrentCellConstruction2011`, `NativeRankVariation`, and their checks: local coefficient cells and exact rank increments.
- Wang tile construction: `WangTiles942HelicalQuotient`, `HelicalExtension`, `HelicalMarker`, `TraceCycle`, `CycleBoundary`, `CycleBand`, `CycleMarker`, `BandMarker`, `FinishConstruction`, `Soundness`, and `Completeness`, each with a companion checks module.

These filenames identify new review surfaces, not recommendations by themselves. Any proposed factoring must still survive the separate all-packets novelty audit.

## Integrity, reproducibility and limitations

- 914 selected current repository files are materialized under `sources/`: all 637 active Lean files, root build/toolchain files, target Markdown, Lean-related and newly changed reviews, script entries, and maintained `generate_` tools.
- Six dependency excerpts are materialized under `dependencies/`: five pre-existing BusyBeaver dependencies rebound through current trees, plus the current lower-level Pell ratio module.
- Eleven authenticated prior-pin files under `comparison_sources/` support complete-file metric replay: the ten modified active files plus old `PellRatio90`.
- Every selected source/dependency/comparison file passed Git blob SHA-1 verification (`blob <byte-count>\0<bytes>`) and carries SHA-256. Reused old bytes were accepted only after matching the current tree's blob SHA.
- `python provenance/verify_snapshot.py` reports zero byte-integrity/coverage/delta failures. This is **not a full repository checkout** and **not a Lean elaboration test**. Lean/Lake was unavailable; no toolchain install, upstream write or repository script execution was performed.
- The recorded source pin remains fixed throughout the review. No claim is made that a later-moving `main` is identical.

## Complete newly incorporated commit list

| UTC time | Commit | Kind | Subject |
|---|---|---|---|
| 16:50:09 | [`47e316fb85`](https://github.com/VladimirReshetnikov/ProveIt/commit/47e316fb854ecea6b25a4b47102eba3b85eadcc6) | proposal intake | Proof simplification proposal(s) |
| 16:52:45 | [`98f4266147`](https://github.com/VladimirReshetnikov/ProveIt/commit/98f426614738d0418719121a2c009967ea0ac280) | proposal intake | Proof simplification proposal(s) |
| 16:55:03 | [`b1c70865cc`](https://github.com/VladimirReshetnikov/ProveIt/commit/b1c70865cc07a81b11a11badf657c5fca4a1bb6e) | proposal intake | Proof simplification proposal(s) |
| 16:56:54 | [`512e0f6a3e`](https://github.com/VladimirReshetnikov/ProveIt/commit/512e0f6a3e7108f32df3c0cd50c06b374b8e8ad6) | new construction | Prove consistency excludes zeros of the literal current 14- and 13-variable equations |
| 16:57:47 | [`fd20de9212`](https://github.com/VladimirReshetnikov/ProveIt/commit/fd20de921254664587de8ec68c3c5ee3e6c1133a) | merge | Merge latest origin/main compiler and mask proof simplifications |
| 16:58:18 | [`d4fd21841e`](https://github.com/VladimirReshetnikov/ProveIt/commit/d4fd21841e0c24ebdcd20384f761ec2cf6ee71e9) | proposal intake | Proof simplification proposal(s) |
| 16:58:42 | [`16af2160de`](https://github.com/VladimirReshetnikov/ProveIt/commit/16af2160de4b66c120fe40bf4d15258f27f04016) | new construction | Extend twisted finite bands to exact helical Wang planes |
| 16:58:51 | [`445f98b0a8`](https://github.com/VladimirReshetnikov/ProveIt/commit/445f98b0a8f73f38a484c4f922507902fc1f453e) | merge | Merge remote-tracking branch 'origin/main' |
| 17:01:43 | [`23f631ea07`](https://github.com/VladimirReshetnikov/ProveIt/commit/23f631ea07fff8632eb8cd92286f7621bbe051c0) | merge | Merge remote-tracking branch 'origin/main' |
| 17:08:23 | [`6a97ba50a3`](https://github.com/VladimirReshetnikov/ProveIt/commit/6a97ba50a3b4a3939d8008dab93183e7e20547c4) | new construction | Construct actual halted trace bands with independent widths and height |
| 17:08:35 | [`50879b9ba2`](https://github.com/VladimirReshetnikov/ProveIt/commit/50879b9ba215ba2e44a1e7e5cfa1b6a7035a7451) | merge | Merge origin/main incoming proof-simplification archives |
| 17:10:50 | [`79bc166a51`](https://github.com/VladimirReshetnikov/ProveIt/commit/79bc166a515bd0f07cac826ad1a1bc1e486c88d2) | adopted simplification | Share generated circuit step and power proofs through checked labels |
| 17:11:12 | [`03ae12b592`](https://github.com/VladimirReshetnikov/ProveIt/commit/03ae12b59276ce4835829d713613cfea1e83a424) | proposal intake | Proof simplification proposal(s) |
| 17:11:19 | [`553a5f7a46`](https://github.com/VladimirReshetnikov/ProveIt/commit/553a5f7a463cbaab8800ff8148fef0bc5a9e1b22) | merge | Merge branch 'main' of https://github.com/VladimirReshetnikov/ProveIt |
| 17:12:04 | [`32b108f214`](https://github.com/VladimirReshetnikov/ProveIt/commit/32b108f2146dc7d6ce1e0c55af9a541a0204a190) | adopted simplification | Share positive and natural nine-coordinate existence transport |
| 17:13:41 | [`be45083ae4`](https://github.com/VladimirReshetnikov/ProveIt/commit/be45083ae446f0206e6979f948900e07c76dc735) | new construction | Close literal marked-word consistency equivalence and derive a unique constructed Start |
| 17:14:01 | [`2effe6f291`](https://github.com/VladimirReshetnikov/ProveIt/commit/2effe6f2916bbbe6308b2b2ea674369a490901d9) | adopted simplification | Simplify radix, convolution and finite-selector proof obligations |
| 17:14:03 | [`e03576e51a`](https://github.com/VladimirReshetnikov/ProveIt/commit/e03576e51a6adcfd8feac05500e1cbcec24c2b33) | merge | Merge origin/main additional archived proof-simplification proposals |
| 17:16:46 | [`0db5a4f906`](https://github.com/VladimirReshetnikov/ProveIt/commit/0db5a4f90697642451cca835d8d72e84c91969c0) | verification/review | Record validated circuit, coordinate and arithmetic simplifications |
| 17:16:47 | [`158eb3cd73`](https://github.com/VladimirReshetnikov/ProveIt/commit/158eb3cd73685be79274c31242a20a9cabe2148f) | merge | Merge commit 'e03576e51a6adcfd8feac05500e1cbcec24c2b33' into codex/zfc-diophantine-consistency |
| 17:17:44 | [`84677f52fa`](https://github.com/VladimirReshetnikov/ProveIt/commit/84677f52fa0ddc5bb683c7b274313b6410927d2c) | verification/review | Record independent replay of the complete native Wang construction |
| 17:20:40 | [`9c5ff75921`](https://github.com/VladimirReshetnikov/ProveIt/commit/9c5ff7592144fb7d8a405bcb5ede7bbe48d9e8a1) | proposal intake | Place twelve more DiophantineConsistency Lean proof-simplification packets |
| 17:20:41 | [`3c182be3a6`](https://github.com/VladimirReshetnikov/ProveIt/commit/3c182be3a662cc3e84d5336f8490d30aed26cfb8) | merge | Merge origin/main generated-proof and coordinate transport reductions |
| 17:22:17 | [`747a97db8c`](https://github.com/VladimirReshetnikov/ProveIt/commit/747a97db8cad9509540d39b674047c4eed603c2a) | new construction | Construct actual local coefficient cells and prove exact rank increments |
| 17:22:59 | [`92667dde60`](https://github.com/VladimirReshetnikov/ProveIt/commit/92667dde6018d6dd902e7177d389ac09d571f4e4) | merge | Merge remote-tracking branch 'origin/main' |
| 17:23:04 | [`7abba93b7c`](https://github.com/VladimirReshetnikov/ProveIt/commit/7abba93b7c4aa2f3a6d2f2fa22db4765e702b4fc) | verification/review | Record independent verification of the actual local coefficient-cell construction |
| 17:26:12 | [`6a7ef347b5`](https://github.com/VladimirReshetnikov/ProveIt/commit/6a7ef347b5bed233fd3ae9e3152df4b05d74fe55) | proposal intake | Proof simplification proposal(s) |
| 17:26:25 | [`1e2a853935`](https://github.com/VladimirReshetnikov/ProveIt/commit/1e2a853935a6155cbcf2aa199aaca51946c4fff9) | merge | Merge branch 'main' of https://github.com/VladimirReshetnikov/ProveIt |
| 17:26:57 | [`8ca6455829`](https://github.com/VladimirReshetnikov/ProveIt/commit/8ca645582907208196b539bf72a8022db4975b67) | adopted simplification | Share ordinary and doubled Pell ratio upper estimates |
| 17:27:27 | [`2f000d10fe`](https://github.com/VladimirReshetnikov/ProveIt/commit/2f000d10febaf13485e0acc4738164691e3b3a40) | merge | Merge commit '7abba93b7c4aa2f3a6d2f2fa22db4765e702b4fc' into codex/zfc-diophantine-consistency |
| 17:27:27 | [`f10019731f`](https://github.com/VladimirReshetnikov/ProveIt/commit/f10019731fd8ef506ea3df64093a21ddc1571e29) | verification/review | Record shared Pell proof validation and rank incoming reductions |
| 17:28:07 | [`2993608983`](https://github.com/VladimirReshetnikov/ProveIt/commit/29936089835c0c55cca81edc86b4fb0c70ce34d5) | proposal intake | Place three more DiophantineConsistency Lean proof-simplification packets |
| 17:28:55 | [`e652d21c41`](https://github.com/VladimirReshetnikov/ProveIt/commit/e652d21c413de59e4821f6e8e9b6a3a077bf5bfe) | merge | Merge commit '29936089835c0c55cca81edc86b4fb0c70ce34d5' into codex/zfc-diophantine-consistency |
