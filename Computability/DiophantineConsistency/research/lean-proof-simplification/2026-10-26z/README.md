# Further Lean proof simplifications for ProveIt

This packet contains four recommendations that survived a mechanism-level audit of the two excluded proposal collections. Prior suggestions are treated as already applied. The complete argument, exact targets, mathematical derivations, counterfactual novelty boundaries and adoption criteria are in **report.pdf** and its editable **report.tex** source.

## Snapshot and exclusions

- Source and standalone-proof pin: `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.
- Expanded exclusion cutoff: `7def5e00ef3593b296eb595add1d955d27121d0c`.
- Delivery recheck: `45ac0dfc366f798d4686070a89d66e8dafdb6879`. Round3 is now packet v; all 22 packets have the same substantive content. Sixteen retained source/dependency blobs remain unchanged. See `audit/DELIVERY_CHECK.md`.
- Lean: `4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- At the substantive exclusion cutoff, the corpus has 21 placed packets (a–u) and one incoming Round3 ZIP: 22 packets. At delivery it contains the same 22 packets placed as a–v. Twelve former incoming packets were relocated to g–r. The audit added s, t, u and Round3 to its initial eighteen-packet review.
- All 15 retained target/dependency files compared across the two commits are unchanged. Other repository files did change.
- Two initially selected ideas were withdrawn after the refresh: centered integer induction and shared-edge/pulse row construction. They receive no new credit and their code/patches are not offered as recommendations.
- `audit/FRESHNESS.md` governs the final novelty classification. `audit/EXCLUSIONS.md` records the broader initial exclusion map. Neither is a claim of novelty outside the audited corpus.

## The four retained directions

| ID | Idea | Evidence and limit |
|---|---|---|
| P1 | Use the vector period `(w,-1)` for helical normalization; period one for seam invariance | Exact helical signature plus generic period-one helper checked. Two-file patch removes 15 physical lines; four of these belong to the seam adaptation whose production integration is unchecked. |
| P2 | Use the fixed chain `A(A²−1)² < A⁵ ≤ x_A(5) ≤ y_A(6) ≤ y_A(p)` | Exact original Pell theorem signature checked; no helper. Patch removes four physical lines. |
| P3 | Derive signal masses symbolically from target counts, sums and rail ranks | Four existing numerical endpoints reproduced in Python. Lean adapter timed out without diagnostics and remains a design prototype; rank/cutoff adapters are future work. |
| P4 | Recognize an arbitrary allowed operating row as the existing `stepTile` row | Source-reviewed canonical-row prototype and stronger local-determinism route. The latter’s exact finite exceptions were checked in Python; no Lean integration or net source saving is claimed. |

The two proposed patches together remove **19 physical source lines**. Of these, **15** occur in replacements whose exact signatures were checked in isolation (11 helical + 4 Pell), and **4** in the seam adaptation supported by the checked generic helper. This is not a full-module certification. No line-saving or speedup estimate is extrapolated to P3 or P4.

## Files

- `report.tex`, `results.tex`, `report.pdf`: complete report and editable LaTeX.
- `lean/checked/`: two successful standalone Lean files; each prints its axioms.
- `lean/proposals/`: three explicitly unvalidated symbolic-mass, canonical-recognition and edge-recognition prototypes.
- `patches/`: exact proposed edits against the source pin, with unchanged public theorem statements.
- `notes/`: additional arithmetic and canonical-recognition details.
- `validation/manifest.json`: authoritative per-artifact status and scope.
- `validation/`: compiler logs, source identities, patch-applicability result, exact line measurements and finite-data results.
- `audit/`: exclusion catalogs, packet/member hashes, candidate searches, freshness review and source-comparison records.
- `scripts/`: portable replay helpers and PDF build script.
- `SHA256SUMS`: hashes of the final archive contents (excluding the hash file itself).

## Replay

Use a prepared checkout at the source pin. Install the toolchain named by its `lean-toolchain` and obtain/build its pinned Mathlib dependencies through the repository's usual Lake setup. The default replay needs only the standalone files' Mathlib imports; it does not require rebuilding all project targets.

```bash
python3 scripts/verify.py /path/to/ProveIt --patches-only
python3 scripts/verify.py /path/to/ProveIt
```

The script verifies selected source identities, the Mathlib pin and Lean version, runs `git apply --check`, and runs the two completed standalone checks through `lake env lean`. It does not apply patches. A source mismatch is reported rather than overwritten.

To attempt the design prototypes, first build their actual production imports in the repository:

```bash
lake build DiophantineConsistency.WangTiles942Core \
  DiophantineConsistency.WangTiles942RowStep \
  DiophantineConsistency.WangTiles942StepConstruction
```

Then, from the extracted packet:

```bash
python3 scripts/verify.py /path/to/ProveIt --proposals
```

This optional command is an integration experiment; success is not pre-certified by this packet. The original review stopped an optional full dependency rebuild before completion under shared resource contention. The final completed checks are recorded explicitly, including the signal-adapter timeout.

The finite arithmetic checks use Python's standard library only:

```bash
python3 scripts/moments.py /path/to/ProveIt --output moments-replay.json
python3 scripts/check_tile_determinism.py /path/to/ProveIt tile-determinism-replay.json
```

The outputs should match the corresponding files in `validation/` as JSON values. These calculations reconstruct the source tile formulas and are independent checks, not Lean kernel proofs. The determinism audit checks all 432 rail-cache entries and the two target lists against the actual 430 actions before classifying all 942 tiles.

To rebuild the PDF, install XeLaTeX with Latin Modern Roman, DejaVu Sans and DejaVu Sans Mono, plus the ordinary packages named in the preamble, then run:

```bash
bash scripts/build_report.sh
```

## Adoption boundary

Review the two small patches first. Build the affected production modules before integration, keeping the original theorem signatures. Next pilot canonical-row recognition and the four-client signal-moment formula independently. For structural changes, count all bridges, helper signatures and compatibility wrappers against the already-shortened baseline. Preserve the literal tile language, halting receiver behavior, wall hypotheses, temporal matching and the independent exclusion of finish tiles.

No remote repository changes are part of this packet.
