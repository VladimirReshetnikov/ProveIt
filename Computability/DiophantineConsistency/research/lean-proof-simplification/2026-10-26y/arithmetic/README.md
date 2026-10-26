# Arithmetic additions for the main report

Reviewed repository commit: 553a5f7a463cbaab8800ff8148fef0bc5a9e1b22.
Lean: 4.32.0. Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997.

Main new proposal: extremal-row pruning in NativeQuadraticPositions.index_span.
The exact source-data fixture and public wrapper compile successfully. The full
NativeQuadraticPositions candidate is supplied for review but was not rebuilt.

Supplementary local cleanup: whole-goal domain normalization in the Sidon proof.
Both the exact replacement statement and the entire modified SidonPositions
module compile successfully. The mathematical factorization itself already
appears in the old source; this is not counted as a new mathematical idea.

Use the paired .patch files to review the exact source changes. The span patch
passes git apply --check at the pinned commit; neither patch was applied to the
production checkout in this session. All existing executable definitions and
public theorem signatures are unchanged.

To replay the source-data fixture using the pinned repository environment:

  cd /path/to/ProveIt
  lake env lean -j1 -R /absolute/path/to/this/lean /absolute/path/to/this/lean/IndexSpanFixture.lean

For SidonMomentCheck.lean, build the original SidonPositions target first and
invoke the same command with the corresponding file. The full modified module
can be checked by applying its patch in an isolated checkout and building its
module. These commands may require the repository's normal dependency setup.

The evidence directory identifies source hashes and exact validation scopes.
Recorded wall times come from a heavily contended machine and are not benchmarks.
