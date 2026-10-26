# Additional Lean proof simplifications for ProveIt

Prepared 26 October 2026 for Vladimir Reshetnikov.

## Main result

The combined patch modifies nine existing Lean modules and adds one shared module.
The selected source shrinks from **1,999 to 1,893 physical lines: 106 lines saved**,
including all added helpers, wrappers, comments, and blank lines.

The proposals were compared with all seven ZIP archives in `docs/incoming` and the
placed packet referenced by its README, at:

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Commit: `7fa06d530df54d4aeb2e18027409df082234c69e`
- Lean: `4.32.0`
- Mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`

The audit records 57 prior-proposal families with precise source/archive references.
“Additional” means no matching proposal was located in that inspected material.
It does not assert global novelty of these mathematical facts or Lean techniques.

## Read first

Open `report/additional_lean_simplifications.pdf`. Its editable source is
`report/additional_lean_simplifications.tex`.

The seven directions are:

1. Preserve the actual rational root when descending an integral nonzero power;
   then share the general separated-root finalizer theorem. **46 lines saved.**
2. A sharp general Pell theorem: a positive solution with second coordinate at
   most three is fundamental. Its first-unit application and helper save
   **8 complete-file lines**, or 14 nonblank proof-body lines.
3. Reuse the existing odd-index theorem in the auxiliary Pell step-down.
4. Compose congruence up to sign instead of rebuilding divisibility witnesses.
   Directions 3 and 4 together save **15 lines**, charging the new 43-line module.
5. Project inverse pairing graphs from the forward graph and its existing
   certificate specification. **27 lines saved** after helpers.
6. Eliminate the zero-test certificate before proving the conditional graph.
   **10 lines saved**, without a new production helper.
7. Optional: recognize the physical permutation as zero followed by an
   injective positive tail. **9 additional candidate lines saved**; excluded
   from the main patch because only the generic schema was compiled.

## Validation actually performed

- All nine package commit pins matched the repository manifest.
- 63 original ProveIt modules compiled from the pinned source.
- All ten main proposed modules compiled in the combined local import tree.
- Seven pairing and two Boolean constructor replacements passed full-value
  equality checks by `rfl` against the originals.
- All 153 existing declaration signatures in the changed files are preserved.
- The integrated axiom audit examined 23 declarations and reported only
  `propext`, `Classical.choice`, and `Quot.sound` (or no axioms).
- The old and new `firstUnit_fundamental` have the same printed axiom set.
- `git apply --check` passed for the combined patch.
- No whole-repository build or performance benchmark was performed.

The main patch is `patches/main.patch`. Complete proposed files are in
`proposed/Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

The optional permutation patch is separate under `optional/`; its full
WangTiles942/K215 client remains uncompiled. It should pass normal project
checks before adoption.

## Replay on the pinned repository

Use a clean checkout at the stated commit. The helper checks the commit and
refuses to run on tracked source changes.

```bash
bash scripts/replay.sh /absolute/path/to/ProveIt --check
```

This performs the patch dry run and the nine baseline constructor equalities.
It builds the necessary original modules but does not apply the patch.

To apply the main patch and build the revised modules:

```bash
bash scripts/replay.sh /absolute/path/to/ProveIt --apply
```

`--apply` explicitly changes the supplied checkout. Run it on a review branch or
disposable checkout. It first checks the baseline, then applies the patch, builds
the modified targets, and runs the integrated axiom audit. It does not commit,
push, publish, or contact other people.

The baseline equality checks intentionally run **before** application. Some
new helper names are present after application, so do not rerun the original
baseline files against the modified namespaces.

The archive records the actual local compiler commands in the evidence JSON.
Those historical paths are not portable; `scripts/replay.sh` is the portable
entry point using the repository's standard Lake environment.

## File map

- `report/`: complete article, LaTeX and PDF.
- `patches/main.patch`: combined checked production changes.
- `proposed/`: all complete main proposed modules.
- `checks/baseline/`: nine original-versus-short constructor equalities.
- `checks/standalone/`: generic proof prototypes, including the sharp Pell bound.
- `checks/IntegratedAxiomAudit.lean`: combined endpoint axiom queries.
- `evidence/`: environment pins, source metrics, compiler receipts and final logs.
- `audit/`: 57-family exclusion map, archive/member hashes, independent reviews.
- `optional/`: permutation candidate and exact client, not fully compiled.
- `scripts/`: portable replay, source comparison, and file-integrity helpers.
- `LICENSE.upstream`: original repository license.

To verify the archive's extracted files:

```bash
python3 scripts/verify_manifest.py
```

To independently recompute the main source counts against the pinned Git objects:

```bash
python3 scripts/source_metrics.py /absolute/path/to/ProveIt
```

## Rebuild the PDF

XeLaTeX was used because this environment's LuaLaTeX font loader is unavailable.
With the usual fontspec, unicode-math, fvextra, and Latin Modern / DejaVu fonts:

```bash
cd report
xelatex -interaction=nonstopmode -halt-on-error additional_lean_simplifications.tex
xelatex -interaction=nonstopmode -halt-on-error additional_lean_simplifications.tex
```

A third run may be needed if the table of contents changes page breaks.

## Practical boundary

These are proof refactorings. They do not reduce witness dimensions, change the
published equation, or establish a new consistency equivalence. The report
distinguishes maintained-source savings from performance, kernel-term size,
and mathematical assumptions. Use the project's usual CI before merging.
