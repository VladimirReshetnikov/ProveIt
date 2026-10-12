# Relative Top-Handle Elimination and the Limits of Forest Optimization

Research continuation for Vladimir Reshetnikov and ProveIt, 12 October 2026.

**Main article:** `article/Relative_Top_Handles.pdf`.
**Complete LaTeX source:** `article/Relative_Top_Handles.tex` and its adjacent sections.
**Repository integration:** `integration/proveit-relative-top-handles.patch`.

This package proves and implements a source-relative elimination of the exceptional three-handles in ProveIt's compressed normal cuts. It also develops an exact abstract forest optimization, proves a homological limitation on that optimization for genuine handle geometry, and gives an exact stopping-set kernel for arbitrary exceptional rows after a fixed forest. It does **not** establish a complete quasipolynomial unknot-recognition algorithm.

## Principal results

1. **Source-relative top elimination.** Every three-handle inherited from an interior source vertex can be removed using exceptional two-handles, while retaining the complete native parallelity interfaces. The proof uses exact source gap ranks, orientation flags, and relative collar geometry. A graph deletion alone would not establish the required marked homeomorphism.
2. **One source tree for every normal cut.** A boundary-rooted source tree specializes to a legal top trace for every admissible normal vector, including the empty vector, one-sided surfaces, and arbitrarily large binary coordinates. The structural schedule is linear in the bounded core; the extra trace has `O(t log(t+2))` bits.
3. **Abstract joint forests and exact deficiency.** When surviving occurrence rows have capped length at most two, the joint top/bottom problem specializes classical two-graphic-matroid partition. The planner emits independent positive schedules or exact rank-deficiency witnesses. Long rows may be forced into the deleted top tree, but this is a restricted strategy.
4. **Homological rigidity on geometric inputs.** The uncapped parity matrices satisfy the boundary-of-boundary identity. After the mandatory rows form a cap forest, every eligible top tree leaves the same short-row cycle nullity, equal to the core's second Betti number over `F_2`. Thus much of the apparent abstract optimization freedom cannot improve authenticated geometry. This conclusion fixes the primal forest and the stated short-row strategy.
5. **Exact exceptional-row kernel.** For a fixed forest, contract the short-row trees, omit the grounded component, and retain exceptional-row incidence signatures. The quotient preserves every exceptional projection of a stopping set. The largest lift is given by minimal short subtrees joining the active exceptional incidence sites and the ground vertex in the grounded component. With `k` exceptional rows, there are at most `3^k-1` distinct nonzero capped column types. This is a structural kernel, not a new one-shot speed claim over already-linear peeling.

The article supplies full proofs, explains which ingredients are classical or already present in incoming work, and proposes twelve focused research questions. `CLAIMS.md` is the integration-facing claim ledger; `RESEARCH_QUESTIONS.md` gives the next research programme separately.

## Measured and independently checked outcomes

| Measurement | Retained result | Scope |
|---|---:|---|
| Complete whole-cut censuses | 85 to 92 of 106 | All earlier successes preserved; seven new certificates |
| Independent whole-cut replays | 92 | Every new complete result rechecked |
| Stored explicit-oracle agreements | 85 | Seven large-coordinate complete cases are not explicitly expanded |
| Former three-handle exclusions | 10 to 0 | Seven become complete; three remain inconclusive for other reasons |
| Largest scheduling benchmark | 47.10 ms to 1.64 ms | 769 tetrahedra, 256 interior vertices; 28.8-fold isolated gain |
| Same case, including common source-incidence reconstruction | 88.42 ms to 45.65 ms | About 1.94-fold; not a full recognizer benchmark |
| Fixed source-template family | 64 compatible vectors | Every specialized trace independently replays |
| Binary scaling | Coordinate size up to 16,385 bits | Additional top certificate remains 193 bytes in the tested family |
| Chain compatibility | 114 authenticated source cores | All satisfy the exact uncapped parity identity |
| Retained kernel replays | 120 | Six abstract examples, 106 corpus cores, eight subdivisions |

The smallest scheduler cases regress, and common source reconstruction dominates the largest new scheduling time. The forest prototype adds **no native coverage** over ordinary core cancellation on the tested corpus. All 114 tested cores have zero second Betti number; the article includes a separate explicit geometric family with nonzero defect. The empirical all-tree check is limited: each of the 42 eligible native packets has a unique mandatory spanning tree. These qualifications matter when interpreting the results.

The final clean integration log is in `evidence/clean_release_check/`; it covers the eight focused modules, not the full repository suite. The initial fast-only harness omitted unchanged repository fixtures; `evidence/initial_fixture_check/` records that resolved packaging issue.

## Baseline and application

The exact base commit is:

```text
8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4
```

The patch changes two maintained files and adds fifteen files. It includes production helpers, three focused test modules, and research scripts. No incoming ZIP is a patch dependency, and none was applied during this work. Apply from the repository root:

```bash
git apply --check /absolute/path/to/package/integration/proveit-relative-top-handles.patch
git apply /absolute/path/to/package/integration/proveit-relative-top-handles.patch
```

The parallel `integration/overlay/` contains the complete resulting source files as an alternative to applying the patch. `integration/manifest.json` records the original hashes of the two modified files and the final hashes of all 17 files. The release patch was applied to a separate pristine baseline snapshot and all 17 outputs were hash-checked.

See `INTEGRATION.md` before changing certificate dispatch. The native validator currently accepts connected orientable triangulations with one torus boundary. The mathematical top-elimination theorem allows arbitrary nonempty boundary, but the implementation does not yet expose that generality.

## Reproduce

The maintained package requires Python 3.10 or later; the retained runs used Python 3.12.14 and Regina 7.4. Regina supplies fresh source triangulations and explicit oracle checks. It is not used as the native certificate authority. Matplotlib is only needed to regenerate the timing figure. A standard TeX Live installation with `latexmk` builds the PDF.

Use an ordinary interpreter without `-O` or `PYTHONOPTIMIZE`, because the research audit scripts intentionally use assertions. Set these variables to absolute paths:

```bash
PACK=/absolute/path/ProveIt_Relative_Top_Handles_2026-10-12
FAST=/absolute/path/ProveIt/Topology/UnknotRecognition/fast
REPRO_DIR=/tmp/proveit-relative-top-reproduction
mkdir -p "$REPRO_DIR"

python "$PACK/tools/run_targeted_tests.py" \
  --fast-dir "$FAST" --output-dir "$REPRO_DIR/focused-tests"
python "$PACK/tools/replay_saved_certificates.py" --fast-dir "$FAST"
python "$PACK/tools/run_forest_exchange_audit.py" \
  --fast "$FAST" --output "$PACK/evidence" --replay-only
python "$FAST/core_top_research/residual_kernel_audit.py" \
  --replay-only "$PACK/evidence/residual_kernel_audit.json"
```

The focused tests also need three unchanged repository fixtures outside `fast/`: `synthesis/data/core-three-handle-probe.json`, `synthesis/data/handle-reducible-trefoil.json`, and `reports/57/results/discovery_corpus.json`, relative to `Topology/UnknotRecognition/`. A normal checkout of the pinned repository includes them. The runner checks these prerequisites before starting and sets `fast/` as the working directory for existing CLI tests.

To rerun the complete kernel audit, its current script requires the forest fixture at a fixed neighbouring path:

```bash
cp "$PACK/evidence/forest_exchange_audit.json" \
  "$FAST/core_top_research/forest_exchange_audit.json"
python "$FAST/core_top_research/residual_kernel_audit.py" \
  --fast-dir "$FAST" --output "$REPRO_DIR/residual-kernel-audit.json"
python "$FAST/core_top_research/chain_audit.py" \
  --subdivision-source "$PACK/evidence/forest_exchange_audit.json" \
  --output "$REPRO_DIR/chain-compatibility-audit.json"
```

The full corpus and local timing commands are in Appendix A of the article. Fresh forest generation without Regina records only the 106 corpus cases; use the saved fixture or install Regina to include all eight subdivisions. Retained matrix replay checks the saved matrix consequences; the native audit additionally reconstructs those matrices from triangulations and normal vectors.

To build the article and optionally recreate its data figure:

```bash
python "$PACK/tools/render_evidence.py"
cd "$PACK/article"
latexmk -pdf -interaction=nonstopmode -halt-on-error Relative_Top_Handles.tex
```

## Files and provenance

- `article/`: complete manuscript, PDF, generated table, and vector/PNG figure.
- `integration/`: reviewable patch, full-file overlay, source manifest.
- `evidence/`: original measurements, source hashes, new proofs, structural audits, clean release logs, and review notes.
- `tools/`: portable test/replay runners, patch builder, figure generator, and archive verifier.
- `SOURCE_AUDIT.md`: exact repository scope and primary literature links.
- `SHA256SUMS.txt`: checksums of all other delivered files.

Intermediate review notes retain the concerns they raised; `evidence/reviews/RESOLUTIONS.md` records the final resolutions. Third-party papers, lecture slides, and incoming archives are linked and hashed where relevant, not redistributed. Code and documentation follow ProveIt's MIT No Attribution license in `LICENSE`.
