# Polynomial Projectors and Compressed Surface Assembly

Research continuation for Vladimir Reshetnikov's ProveIt unknot-recognition program, 8 October 2026.

**Read the article:** `article/unknot_projectors_and_seams.pdf` (31 pages). The complete LaTeX source is alongside it, with all included tables and the figure. The article contains proofs, implementation contracts, exact and empirical comparisons, a conditional global complexity analysis, and fourteen proposed research topics.

**Status:** two exact decomposition kernels are implemented and validated. A general quasipolynomial unknot recognizer is **not** established. The primary backend is optional. The geometric kernel has a precise restricted surface-cover input model and does not issue knot verdicts.

## Main results

1. A polynomial-projector extension of scalar Fitting splitting, using Berlekamp's classical Frobenius fixed algebra. The positive witness checks the complete typed differential and every attachment. The new API is `recognize(..., backend="primary")`; the exact-rank CLI is `khovanov --primary`.
2. A connected graded algebraic family with scalar commutant `F_(2^r) × F_(2^r)`. Independent uniform candidates succeed with probability `2(2^r−1)/2^(2r)` under the old stable-kernel test and at least `1−r/2^r` under the polynomial-projector test. No realization as a classical-knot prefix is proved; the production candidate policy is not uniform sampling.
3. Exact full-boundary assembly of dihedral surface covers with binary sheet counts. The kernel verifies seam equations, retains original port and marking provenance, and computes topology without enumerating sheets. It handles valid closed and nonorientable outputs, including the one- and two-sheet degeneracies.
4. A proved, unimplemented next optimization: child scalar commutants are the corner algebras `e_i R e_i`. A complete parent basis can be transported and restricted instead of re-solving the differential equations. The article gives dimension and static transport bounds and identifies the costs still to be measured.

## What the measurements support

- All five natural-knot raw scans have **zero primary calls and zero primary splits**. No natural-knot speedup is claimed.
- Dense algebraic examples at `r=8,10` fit the unchanged default caps and split after two candidates where the old bounded pass finds no split after 32 or 36. Search-pass time ratios are about 2.62 and 2.54. Complete recursive compression shows no material speedup, although it reduces differential entries from 142 to 75 and 221 to 102.
- On the 65,536-sheet examples, compressed geometric preparation takes about 0.086 and 0.123 ms, versus 292 and 309 ms for an independent literal-sheet oracle. This measures avoided expansion, not a comparison with another compressed normal-surface algorithm or a knot-recognition speedup.
- At `W=2^16384` with 64 patches, preparation takes about 3.571 ms. Output size is still charged: the serialized summary is 782,029 bytes.

All displayed measurements come from `evidence/*.json`. The article defines the distinct pairing and denominator conventions. Raw samples, input constructions, witnesses, operation counts, A/A controls, and output sizes are retained.

## Contents

| Path | Purpose |
| --- | --- |
| `article/` | Main TeX and PDF, generated tables, static plot, bibliography |
| `source/Topology/UnknotRecognition/fast/` | Complete relevant updated package, tests, fixtures, and research drivers |
| `source/Topology/UnknotRecognition/reports/` | Three historical oracle dependencies used by existing tests |
| `baseline/` | Pinned source snapshot sufficient to replay the patch |
| `integration/changes.patch` | All production, test, fixture, and driver changes against the pinned commit |
| `INTEGRATION.md` | API examples, scope, compatibility, and integration instructions |
| `evidence/` | Retained raw measurements and exact measured geometric sources |
| `validation/` | Complete final and baseline suite logs, focused worker and geometry logs, build and packaging checks |
| `scripts/reproduce.py` | Hash verification, patch replay, complete tests, optional benchmark reruns |
| `scripts/make_figures.py` | Regenerate all numerical tables and the plot from retained evidence |
| `SOURCE_MANIFEST.json` | Pinned provenance and source/baseline hashes |
| `SHA256SUMS` | SHA-256 manifest for every distributed file except itself |

Historical benchmark-result files unrelated to this continuation and Python caches are omitted. Required test inputs are included.

## Reproduce

From this directory:

```bash
python scripts/reproduce.py --verify
python scripts/reproduce.py --tests
```

The first command requires Git, checks every distribution hash, checks the exact measured geometric sources, and applies the patch to a temporary baseline copy. It requires the result to match the supplied updated source byte for byte. The tests use Python's standard library. The recorded environment is Python 3.12.14 on Linux x86-64. Three actual native-engine tests need the optional Regina dependency.

The final complete run executed **729 methods: 726 passed, 3 skipped**. The added geometry suite performs 1,547 topology comparisons and 6,216 ordered-mark comparisons against an independent expanded oracle. The twelve primary tests include exhaustive small polynomial/matrix cases and full differential attachments. Five further methods test public primary integration; one tests invalid worker bytes. The baseline had 697 methods and an existing partial-input worker error.

To rerun the timing experiments, explicitly request:

```bash
python scripts/reproduce.py --benchmarks
```

Fresh files are written to `rerun_results/`; retained evidence is preserved. Timing values will vary. The geometry driver's metadata fallback was made portable after the measured run; the exact measured version is included separately and its hashes are checked. Arithmetic kernels and timed operations were unchanged by that metadata-only edit.

To rebuild the article, install Matplotlib and a LaTeX distribution with the packages named in the preamble, then run:

```bash
python scripts/make_figures.py
cd article
pdflatex -interaction=nonstopmode -halt-on-error unknot_projectors_and_seams.tex
pdflatex -interaction=nonstopmode -halt-on-error unknot_projectors_and_seams.tex
```

Run hash verification **before** regeneration, since regenerated PDF metadata and local logs may differ. The ZIP includes a ready-to-read PDF and all figure assets; regeneration is optional.

## Provenance and integration

Baseline: `bc5b913850f78155ccfddd808d4b11517dca252d` in <https://github.com/VladimirReshetnikov/ProveIt>.

The one-submit threaded subprocess repair comes from the earlier incoming `unknot_certified_primitives_20261008.zip` report and is credited accordingly. This continuation adds a small malformed-byte failure-handling regression and correction. Regina remains an explicitly external engine; no independent normal-surface certificate is claimed.

Classical ingredients, including Berlekamp's full primary-factor refinement and covering-space monodromy, are attributed in the article. The prose proofs and model-agent mathematical reviews are not proof-assistant certificates or journal peer review. The source snapshot, validation, and narrow positive checkers are provided for repository review and further formalization.

No remote commit, pull request, or push is included in this delivery. The patch and article are ready for local integration and review. The included MIT No Attribution license matches the existing `fast` package.
