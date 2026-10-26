# Round 7: exact source, recent history, and bounded closing screen

## Frozen scope

- Repository: `VladimirReshetnikov/ProveIt`.
- Source commit: `7ba7d102822df1eff376cbca913727d9d588ab4e`, committed **26 October 2026, 19:25:35 UTC**.
- Commit root tree: `3d4c4989af0d7e80ea0e631a7ca5ce5a7b9aad39`.
- Active Lean tree: `ced7dfca204e0fe30283ffa7e60e24b34646b301`.
- `sources/`: all **724 blobs** of the complete active Lean subtree, plus **8** configuration/context files. The recursive tree contains 726 entries, with `truncated=false`.
- `dependencies/`: **29** files: all **26 direct external repository imports** of the active subtree, plus `SignInvariantPolynomial`, `Pell`, and `PellMod`. This is **not** a full transitive dependency closure or a Mathlib checkout.
- `comparison_sources/`: **19** exact historical files: 12 at the round-6 source pin and 7 at its closing pin.
- `provenance/review_sources/`: **20** exact repository review documents. Compiler observations in these documents are their authors' historical reports, not checks performed in this session.
- Toolchain text: `leanprover/lean4:v4.32.0`. Lean and Lake are unavailable; no installation, elaboration, Lake build, repository write, or upstream mutation was attempted.

## Portable verification

From the packet root, run:

```sh
python -O provenance/verify_snapshot.py
```

The verifier uses explicit conditional checks, not Python `assert`. Both ordinary Python and `python -O` passed. An isolated-directory replay using only the **854 files** listed in `source_replay_inputs.json` also passed. Eight corruption/omission tests failed as required, including missing source, modified source, missing imported theorem bytes, a truncated-tree flag, a false tree hash, a false closing target blob, an omitted timeline commit, and an omitted dependency entry. See `verification_result.json`, `portable_verification_result.json`, and `negative_verification_result.json`.

The verifier reconstructs **33 Git tree snapshots**, checks ancestor bindings, verifies the Git-blob SHA-1, SHA256, size/physical-line counts and exact materialized coverage of **800 files**, checks both source deltas and parent-graph commit sets, and binds both closing candidate files. It verifies the bundled evidence against saved GitHub receipts; it does not independently authenticate GitHub, prove Lean theorems, establish proposal novelty, or claim a complete Lake checkout. The proposal audit has its own independent verifier.

## Exact comparisons with round 6

| Baseline | Ahead commits | Added active files | Modified | Removed |
|---|---:|---:|---:|---:|
| Source `9d9d1123b39927d30363f1dcd53c23f0575c30ee` | 23 | 22 | 12 | 0 |
| Closing `451b548a198c791e81abc40435979c89edb40b23` | 13 | 22 | 7 | 0 |

File deltas come from complete, independently hashed Git tree objects, **not** capped GitHub compare file arrays. Commit sets come from the pinned 100-commit parent graph; their unresolved frontier is outside the claimed differences. Counts are corroborated with compact GitHub compare metadata. See `active_tree_delta.json`, `since_closing_delta.json`, `commit_timeline.json`, and `since_closing_commit_timeline.json`.

### Already adopted upstream reductions—not round-7 discoveries

| Module | Round-6 source → frozen source lines | Net removed | Already present at round-6 closing? |
|---|---:|---:|---|
| `ExecutableJones` | 300 → 251 | 49 | Yes |
| `JonesSyntax` | 179 → 179 | 0 | Yes |
| `NativeQuadraticPositions` | 258 → 177 | 81 | Yes |
| `ObjectPolynomial` | 98 → 82 | 16 | Yes |
| `SyntaxCoefficients` | 120 → 110 | 10 | Yes |
| `AnnotatedAssumption` | 97 → 89 | 8 | No |
| `AnnotatedBound` | 325 → 321 | 4 | No |
| `AnnotatedProofChecker` | 380 → 376 | 4 | No |
| `AnnotatedRename` | 369 → 365 | 4 | No |
| `AnnotatedRuleSide` | 75 → 67 | 8 | No |
| `SelectiveCoefficientBounds` | 211 → 209 | 2 | No |
| **Total** | **11 modified module files** | **186** | **30 since closing** |

These are exact physical-line differences, not newly claimed proof savings. The aggregate import module separately grows from 358 to 369 lines. The 22 new files add 2043 lines of mathematical work and checks; they are not negative simplification savings.

The new module/check pairs are `ControllerRankStride`, `CurrentFiniteDummyMutation2011`, `CurrentHaltPacking2011`, `CurrentPackingParity2011`, `CurrentPositiveZero2011`, `CurrentRankCalibration2011`, `CurrentRankStride2011`, `CurrentSafeController2011`, `NativeOuterSeedConstruction`, `NativePositiveSourceConstruction`, and `WangTiles942ControllerDimensions`.

## Candidate theorem availability

`candidate_import_route.json` records an exact existing import route from `NativeHalfBinomial` through `NativePellScaleBounds`, `NativeBinaryScale`, `NativePellPower`, `NativePellFirstIndex`, `NativePellBootstrap`, `NativePellStepDown`, `SignedPellResidue`, and `PellInt` to `PellMod`, then `Pell`. Every file on this route is included and Git-blob verified. `PellMod` contains `Diophantine.lt_yn_of_two_le`; its exact Git blob is `0e669cfca380d4318038d814f1485ea70f410afe`. This is source/import evidence, not an elaboration result for a proposed replacement.

## One bounded closing screen

Main was observed once at `3b51c69d42ff99bc420698532af3fe1d1f9bd356` (**19:32:32 UTC** commit time). Every subsequent closing read used that immutable commit/tree. The frozen source was not moved and main was not polled again.

- Closing root: `6532ae247e0236a798bae951cb26d52652b36f28`.
- Closing active tree: `aabaff7b520ecdc39ea3c0212b0471f18a5ce7d1`.
- `NativeOuterSeedConstruction.lean` remains whole-file identical at blob `c02b1abb2c0b9c9c75b63ddd618c5ff678f0911b`.
- `SelectiveCoefficientBounds.lean` remains whole-file identical at blob `d6a0738ca9593a19637f4e8fe0ce7e76aa8b72ec`.
- Five other active files changed: `ArithmeticNonzero`, `CurrentKernelResidues2011`, `CurrentPowerCoordinates2011`, `PrimePowerOrder`, and `WangTiles942PhysicalOrder`. None were added or removed. Their exact closing blob delta is retained in `CLOSING_active_tree_delta.json`; their closing bytes are not substituted into the frozen sources.

Closing source equality is not a proposal-exclusion verdict. The separate proposal audit examines the closing research/incoming inventory.

## Acquisition and reuse

All fresh repository source and metadata reads used the GitHub connector. Exact prior bytes were reused only after Git-blob verification against the current pinned tree. Every reused active file and dependency is labeled in its manifest; `reuse_receipt.json` documents reused immutable tree/baseline receipts. The 14 dependency ancestor receipts are reused because their exact current-root subtree IDs are unchanged, and all hashes/ancestor edges are replayed. The round-6 closing active tree and every round-7 closing tree were fetched by exact immutable Git tree IDs.

The compact source replay is approximately 2.2 MB compressed (the full curated packet may include additional research/audit evidence). Raw duplicated tool envelopes, acquisition pending lists, and helper scratch files are not needed for portable source replay; `source_replay_inputs.json` is its complete input closure.
