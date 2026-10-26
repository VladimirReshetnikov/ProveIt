# Further Lean proof simplifications

Prepared 26 October 2026 for the ProveIt DiophantineConsistency development.

**Pinned repository commit:** `efa64ca941cdae37bb6f7fc5093ae8bb69296ca3`  
**Lean:** 4.32.0  
**mathlib:** `81a5d257c8e410db227a6665ed08f64fea08e997`

Read `report.pdf` for the complete analysis. Its editable LaTeX source is `report.tex`.

## Results

Five additional directions contain six concrete mechanisms: reuse five existing Jones evaluation lemmas; prove the auxiliary norm bound through a positive gap; share one affine carrier domination theorem; reduce the helical theorem to periodicity; identify monomial-list interpretation with list sums; and eliminate deterministic function witnesses in composition.

The proposed patches remove **94 physical Lean lines across eight files**, including helper, import, documentation, and spacing costs. They preserve existing executable definitions and public theorem statements. Five previously private Jones theorem names and one new carrier helper become public. The current equation, variable counts, and encoded program data are not changed.

| Group | Net lines removed | Completed validation |
|---|---:|---|
| Jones semantic API | 49 | Exact-definition harness plus source comparison; full modules not rebuilt |
| Carrier norm gap and shared affine bound | 16 | Exact replacement theorem bodies and helper; full modules not rebuilt |
| Helical periodicity | 10 | Exact theorem and stronger factorization; full tile module not rebuilt |
| Monomial-list sum interface | 9 | Entire replacement module compiled |
| Deterministic function witnesses | 10 | Both full modules compiled; full old/new constructor records equal by `rfl` |
| **Total** | **94** | **19 lines in full-module-compiled edits; 75 in narrower checks** |

The earlier 22 a–v packets are treated as already applied for novelty screening, regardless of their adoption status. Counts are exact against the pinned source snapshot; they are not a claim that all competing historical patches were simultaneously merged and replayed. The incoming directory currently contains its retirement index rather than the old binary archives. The scope and rejected ideas are documented in `evidence/novelty_audit.md`.

## Contents

- `patches/proposed.patch`: combined patch against the pinned snapshot.
- `patches/01-jones-evaluation-api.patch` through `04-deterministic-and-helical.patch`: component patches.
- `baseline/`: original copies of the eight affected source files.
- `replacements/`: complete replacement sources at their repository-relative paths.
- `lean/CarrierKernels.lean`: exact carrier replacement theorem blocks and helper.
- `lean/StructuralKernels.lean`: generic helical theorem, unique factorization, and function-witness lemma.
- `lean/JonesBridgeHarness.lean`: harness using the actual pinned source definitions.
- `lean/CompositionCompatibility.lean`: reconstruction of both original composition constructors and whole-record `rfl` equalities.
- `evidence/`: compiler receipts, independent review, novelty ledger, source authentication, metrics, and provenance.
- `provenance.json`: exact before/after source hashes and validation scopes.
- `SHA256SUMS`: checksums for the delivered files.

## Verify the package without a Lean installation

From the extracted package directory:

```bash
python3 scripts/verify_artifact.py
```

This verifies file checksums, baseline and replacement hashes, line totals, successful application of the combined patch to temporary copies, and exact agreement with the supplied replacements. It does not modify a repository. Python 3 and Git are required. An optional `--repo /path/to/ProveIt` also checks that the corresponding files there match the recorded baseline, without changing them.

## Replay the completed Lean checks

Use a ProveIt checkout with its pinned Lean/mathlib environment already set up:

```bash
bash scripts/replay_kernels.sh /path/to/ProveIt
```

The script builds `Representation` and `ArithmeticRepresentation` through that checkout's Lake configuration, then compiles the three full replacement modules into a temporary output directory and replays the four supplied kernels/harnesses. It does not overwrite maintained source files. Lake may update ordinary build outputs in the supplied checkout. This replay has the same limited scope as the report; it does not rebuild the full Jones, carrier, or Wang dependency graphs.

For integration, apply selected patches on a working branch, rebuild all eight affected modules, then run their direct clients and the project's existing checks/axiom audits. The package's exact-source comparisons are useful gates, but not a substitute for this larger replay. No runtime or elaboration speed improvement is claimed.

## Rebuild the PDF

```bash
bash scripts/build_report.sh
```

This requires XeLaTeX with the packages listed in `report.tex`, Latin Modern fonts, and DejaVu Sans Mono. It runs the compiler twice to resolve references and the table of contents.

## Provenance and licensing

Repository sources were read at the pinned commit. Independent GitHub tree checks authenticated 1,763 retained text files without mismatches. The source-based Jones harness also records its two HilbertTenthProblem dependencies. Existing compiled Mathlib dependencies were reused; a source rebuild of Mathlib is not claimed.

`LICENSE-ProveIt.txt` preserves the repository's MIT No Attribution notice for its included source material. The report and new helper proofs are provided for incorporation into ProveIt.
