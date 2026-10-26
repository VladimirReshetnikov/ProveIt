# Round 5 current-source binding

## Exact snapshot and scope

- Repository: VladimirReshetnikov/ProveIt.
- Frozen commit: `e1c8914bc7064d9a8e7c06171a18069a949badd0`, authored 2026-10-26 18:30:35 UTC.
- Actual commit root tree: `d940f73e1bb88de37852cfc86c06540fda01930f`.
- Active DiophantineConsistency Lean subtree: `dbb7c31437172362154f83f200624defc459f32f`.
- Complete active tree: 690 Lean blobs, including check modules; 692 entries including directories. All active blobs materialized.
- `source_manifest.json`: 697 bound files (690 Lean, four root configurations, three contextual documents).
- `dependency_manifest.json`: 27 bound direct external repository imports plus SignInvariantPolynomial. This is deliberately not a transitive dependency closure and is not a build environment.
- `comparison_manifest.json`: old versions of the 32 modified active modules, with old Git blob and SHA256 bindings.
- No AGENTS.md was present in the repository root, Computability, DiophantineConsistency root, active recursive Lean subtree, or fetched dependency directories. No local AGENTS.md was found in this workspace.

GitHub connector calls obtained the pinned directory/tree and history data. Immutable raw GitHub source downloads were accepted only after recomputing the Git blob SHA1 against those tree entries. Unchanged round-4 bytes were reused only when the freshly fetched current tree's blob SHA matched their recomputed hash. Every delivered source has a SHA256 binding as well.

## Complete deltas, not compare-file-array guesses

Against the previous source `e652d21c413de59e4821f6e8e9b6a3a077bf5bfe`:

- 47 commits ahead, 0 behind.
- Active files: 637 to 690.
- Exactly 53 added, 32 modified, 0 removed active Lean files.
- Exact tree-to-tree list: `active_tree_delta.json`.
- Active physical lines: 80,328 to 86,351. The +6,023 net lines reflect substantial new construction plus refactors; they are not proof-simplification savings.

Against the last closing screen `09d65a93c9df8684c1a226341d6a5120623d1cdb`:

- 25 commits ahead, 0 behind.
- Active files: 664 to 690.
- Exactly 26 added, 26 modified, 0 removed active Lean files.
- Exact tree-to-tree list: `since_screen_delta.json`.

The compare metadata supplies ancestry/count checks only. Its file array was not used to determine the active changes. The complete fresh Lean trees, their directory lists, and their raw Git object hashes determine the deltas.

## Recent adoption screen

The following upstream commits and current-source changes are evidence that these families must not be presented as new round-5 proposals. The descriptions are commit subjects plus source-level observation, not independent Lean verification:

| Commit | Existing/adopted family |
|---|---|
| `025c99b12c07` | Shared signed integer-root recovery across finalizers |
| `f7794ed51a0c` | Internal natural cases in zero-sum and zero-product proofs |
| `15295203798b` | Pairing projection facts across graph certificates |
| `4de06108b31c` | Coefficient-envelope proofs across the 22 native rows |
| `2ed7cc3ebbc2` | Raw-parent reconstruction and tree-decoder invariants |
| `292413824977` | Evaluator transport and positive carrier wrappers |
| `4261a5e35353` | Core Option.map injectivity in parent lookup |
| `3814a1da29db` | Extracting internal ZF axioms from sealed ZFC models |
| `f1b8c4abc36d` | Integer unit/nonnegative sum/norm obstruction library lemmas |
| `fad90f705b0b` | Isolated coefficient calculation across quadratic encoders |
| `dbc6446fa790` | Fixed-state and seed-shift numeric scanner inductions |
| `4ae1ff991a03` | Direct object arithmetic semantics simplification |

`02220dfb41a4` records upstream checking of several refactors, but this research snapshot has not run Lean. The complete chronological, parent-linked 47-commit summary is `commit_timeline.json`. The exact 25-commit difference since the closing screen is `since_screen_commit_timeline.json`, selected by parent-graph ancestry rather than a chronological prefix (three side-branch commits predate the screen).

Largest modified-file reductions between snapshots are NativeCoefficientBounds 679→127, MarginFinalizer 177→135, ObjectCodeBound 476→435, AnnotatedParents 165→129, and ShortSystem 558→526 physical lines. These are exact whole-file differences only, not attributed gross/net proposal savings.

## Fresh residual search map (not recommendations)

Newly constructed code offers a better novelty pool than pre-existing scanner/finalizer/carrier families. Priority modules at the frozen pin:

- CurrentKernelResidues2011: 843 lines, new after the closing screen; literal residue derivations and arithmetic/cast scaffolding.
- CurrentControllerUnits2011: 201 lines, new after closing; two parallel fixed-prime power-dimension proofs, quadratic residues, coupling residues, coprimality assembly. The small parametric power proof is only a possible target and must pass prior-art screening.
- CurrentDummyMutation2011: 193 lines, new after closing; source update, normalized increment, and existential witness packaging.
- CurrentWordPadding2011: 224 lines; newly added after closing, word-zero/padding cases.
- CurrentWordScalarWitness2011: 156 lines; new after closing, scalar witness assembly.
- CurrentWordCopies2011: 217 lines and CurrentWordTopBounds2011: 259 lines; new since previous source but already present at closing screen. Prior round proposals may already cover them.
- PrimePowerOrder, ControllerPowerCoordinates, CurrentAuxiliaryOrder2011, CurrentPowerCoordinates2011: smaller generic-versus-specialized arithmetic interfaces.
- SidonPositions: 168 lines and IterationSize: 163 lines; unchanged source blobs, requested for residual inspection; not automatically novel.

All earlier proposal families remain excluded even if their implementation is absent. This file maps source and history; it does not replace the complete prior-proposal screen.

## Replay and limits

Run `python provenance/verify_snapshot.py` from anywhere. It checks raw Git tree hashes, ancestor links, both snapshots' blob/SHA256 bindings, exact active coverage, two complete deltas, and per-file line counts. `verification_result.json` records zero failures.

No Lean executable was invoked, no dependencies were installed, no repository/branch/PR files were changed, and no CI or proof-elaboration success is claimed. Files here are a local research snapshot only. No blocker remains for source acquisition.
