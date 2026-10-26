# Further Lean proof simplifications for DiophantineConsistency

Prepared 26 October 2026 for Vladimir Reshetnikov.

Read `report.pdf` for the complete ten-page analysis. Its self-contained source is `report.tex`.

## Findings

The packet contains six narrowly scoped ideas screened against all 23 placed earlier packets and all five incoming ZIPs at the reviewed revision. Prior proposals are treated as already applied, including uncompiled and deferred suggestions.

| ID | Target | Change | Measured physical lines saved |
|---|---|---|---:|
| P1 | `WangTiles942PhysicalOrder.strictMono_fin_eq_self` | Finite-chain rigidity through `OrderHom.eq_id_of_injective` | 25, including a new direct import |
| P2 | `ControllerIntervalSums.interval_injOn` | Canonical bounded representatives via `Nat.ModEq.eq_of_lt_of_lt` | 3 |
| P3 | `ControllerResidueLift.exists_coordinate` | Normalize `castHom` before taking `ZMod.val` | 5 |
| P4 | `ControllerAuxiliaryChoice.exists_coprime_cardinality` | Nondivisibility and positive representative via exact `ZMod` lemmas | 5 |
| P5 | `ArithmeticNonzero.Rep.nonzero.correct` | Square positivity and integer discreteness instead of sign splitting | 3 |
| P6 | `CurrentCarryConstruction2011.assembled_source_pos` | Positivity from a selected digit; remove stride and marking arguments | 3 with API migration |

P1-P5 remove 41 lines. With the recommended P6 signature migration, seven complete target files change from 609 to 565 physical lines: **44 lines removed**. P6 changes a public theorem's arity and migrates its sole actual maintained check call. External callers using the old final two arguments must drop them.

P6 also has a mutually exclusive compatibility alternative: introduce `assembled_source_pos_unmarked` and preserve the old marked theorem as a wrapper. That alternative **adds 10 lines**; do not count the wrapper's shorter body as a net reduction. The 44-line figure uses the API migration, not the compatibility alternative.

These are measured textual changes at the reviewed source. They are not projected cumulative savings after arbitrary implementations of earlier proposals, performance improvements, or a new Diophantine consistency result.

## Exact source and toolchain pins

- Review base: `7df43cdfacb490cd3ca3acd23e39027efebf8801`.
- Closing main-branch refresh: `663fb267f6142ca4c0ea5bcd2d4f607f9a4b0eda`.
- Repository: <https://github.com/VladimirReshetnikov/ProveIt>.
- Lean: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.

All seven target files are byte-identical at the two repository pins. The only changed file in the prior-proposal directories was the adoption ledger; there were no new manuscripts, patches or incoming archives. See `evidence/refresh_audit.json`.

## What was checked

- P1: the exact original and replacement generic theorem declarations compiled. A finite-linear-order generalization and empty/singleton cases compiled. Axiom lists agree.
- P2-P4: standalone old/new proofs compiled; an independent reviewer compiled the three replacements. Four complete controller modules, all four original focused check clients, and a boundary/axiom harness passed: **nine successful invocations**.
- P5: the exact original and replacement arithmetic goal compiled. Axiom lists agree; expression data and witness count are unchanged.
- P6: the weighted-sum kernel and source-shaped adapters compiled, including the exact two-line proof shape and single-cell examples with arbitrary natural controls. Actual source binding remains an integration check.
- All five individual alternative/independent production patches pass `git apply --check` at the pinned checkout. The recommended combined patch was checked as well.

**The entire maintained ProveIt dependency closure was not rebuilt.** The controller replay is isolated: it replaces the broad `Mathlib.Tactic` import by `Mathlib.Algebra.BigOperators.Ring.Finset` in its validation copy and explicitly imports `Mathlib.Tactic.NormNum` and `Mathlib.Tactic.NormNum.Prime` in its validation check copies. The production patch retains all original controller imports. This accommodation contributes no claimed source saving.

Checked named theorems use only the standard axioms listed in their receipts. In particular, coordinate lifting uses `propext` and `Quot.sound`; the other checked replacement kernels also use `Classical.choice`. There is no `sorry`, new axiom declaration or `native_decide` in the proposed proofs. This is a scoped audit of these proofs, not a new certification of all imported source.

## Archive layout

- `report.tex`, `report.pdf`: full report and source.
- `lean/`: eight standalone original/replacement/boundary proof files.
- `patches/`: independent patches, the recommended combined patch, and the alternative P6 compatibility patch.
- `overlays/production-before/`: exact original files at repository-relative paths.
- `overlays/production-after/`: complete proposed files for the recommended combination.
- `overlays/compatibility/`: alternative complete P6 module preserving the old signature.
- `overlays/controller-validation/`: source and check inputs for the isolated controller replay.
- `evidence/`: measured costs, source/ZIP hashes, overlap catalog, compiler receipts, closing refresh, and independent review.
- `tools/`: integrity, patch-applicability, proof-kernel and controller replay scripts.
- `MANIFEST.json`: file sizes and SHA-256 hashes for the delivered bundle.

## Read-only checks and replay

All replay commands assume the pinned toolchain and required dependency objects are already present. They download nothing and do not apply patches.

From the unpacked bundle:

```bash
python3 tools/verify_artifacts.py
python3 tools/verify_artifacts.py --repo /absolute/path/to/ProveIt
python3 tools/replay_kernels.py --project /absolute/path/to/pinned/Lean/project
```

The optional `--repo` check verifies each baseline target hash, measures the before/after files, and checks patch applicability. It accepts a repository with matching target bytes, including either reviewed pin. It writes no repository files.

The standalone kernel replay uses the project's `lake env lean` and writes its receipt to `kernel-replay.json` by default. Supply `--output` for a different receipt location. It checks both original and replacement proofs where provided, without requiring the ProveIt module closure.

To replay the full isolated controller chain and its clients:

```bash
python3 tools/controller_replay.py \
  --mathlib-root /absolute/path/to/mathlib4 \
  --lean-bin /absolute/path/to/lean-4.32.0/bin \
  --output controller-replay.json
```

The controller script builds only disposable temporary modules and deletes them afterwards. Its nine successful checks are already recorded in `evidence/controller-validation.json`.

## Production integration

Use a disposable checkout of ProveIt at one of the reviewed commits. For the recommended combination, first check and then apply:

```bash
git apply --check /absolute/path/to/bundle/patches/recommended.patch
git apply /absolute/path/to/bundle/patches/recommended.patch
```

Alternatively apply these first three patches independently, then choose one P6 patch:

1. `finite-order-rigidity.patch`
2. `controller-cast-normalization.patch`
3. `semantic_arithmetic_nonzero.patch`
4. **Choose one:** `source-selection-api-migration.patch` or `source-selection-positivity.patch`.

**Do not apply both P6 variants, and do not apply individual patches after the combined patch.**

Complete integration by building the actual maintained modules and existing clients through ProveIt's ordinary Lake setup. The direct targets include:

```bash
lake build DiophantineConsistency.WangTiles942PhysicalOrder
lake build DiophantineConsistency.ControllerIntervalSumsChecks
lake build DiophantineConsistency.ControllerOrbitTransportChecks
lake build DiophantineConsistency.ControllerAuxiliaryChoiceChecks
lake build DiophantineConsistency.ControllerResidueLiftChecks
lake build DiophantineConsistency.ArithmeticNonzero
lake build DiophantineConsistency.CurrentCarryConstruction2011Checks
```

Also run the repository's normal relevant downstream checks. These commands are integration instructions; the report does not claim they were executed against the full maintained dependency closure here.

## Rebuild the PDF

The report uses XeLaTeX, `fontspec`, `fvextra`, standard AMS packages, and DejaVu fonts:

```bash
latexmk -xelatex -interaction=nonstopmode -halt-on-error report.tex
```

## Novelty audit limits

The audit covers 23 placed packets and all five incoming ZIPs: 2,329 files/member payloads, 2,161 searchable text files, and 175 overlapping exclusion records. It includes all main manuscript section indexes, proposal descriptions and inherited exclusion catalogs, relevant technical notes, and candidate-specific searches and reading. It is not a fresh semantic verification of every old implementation or every historical external link in the incoming index. All earlier proposal statuses are treated as prior, as requested.

Source changes, pending status, narrower proof counts and optional alternatives are documented explicitly. No commit, pull request or remote repository mutation was made during this review.
