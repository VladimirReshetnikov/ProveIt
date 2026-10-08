# reports

The six original archives and their extracted contents. Each ZIP had a single
wrapper directory, which was removed; the numbering follows the archives'
modification times.

| Dir | Archive | Package | Complete recognizer | Hierarchy components | Tests |
|---|---|---|---|---|---|
| `01/` | `unknot_recognition_implementation.zip` | `unknot` | grid diagrams, Dynnikov moves, replayable certificates | ball-pattern test, rational H^1, cocycle-dual normal coordinates, potential | 40 |
| `02/` | `unknot_recognition_partial_implementation.zip` | `unknotlab` | descending test, determinant, reduced Khovanov cube over F2 | face-pairing triangulations, normal coordinates, ball-pattern test, potential | 64 |
| `03/` | `unknot_workbench.zip` | `unknot_lab` | determinant, Khovanov cube with default ceilings | bond-enumeration pattern test, conditional bound arithmetic | 49 |
| `04/` | `unknot_recognition_partial.zip` | `unknot` | Khovanov cube, Knot Atlas fixtures | dual-4-connectivity pattern test, potential | 62 |
| `05/` | `unknot_recognition_partial_implementation (1).zip` | `unknot_recognition` | Reidemeister I/II traces, determinant, Khovanov cube | bond-enumeration pattern test, simplicial normal coordinates, pattern complexity | 58 |
| `06/` | `unknot-recognition-implementation.zip` | `unknot` | Khovanov cube, 11-crossing fixtures, report verifier | bond-enumeration pattern test | 45 |
| `07/` | `unknot_structural_compression.zip` | `fastunknot` 0.3.0 (`07/fast/`) | signed-Seifert-graph certificate stage, exact component-sharing Khovanov backend | Euler/component scans | 69 integrated tests pass |
| `08/` | `unknot_recognition_progress.zip` | `fastunknot` 0.3.0 (`08/Topology/UnknotRecognition/fast/`, `code_changes.patch`) | complete decision for closures of braids on at most three strands (`O(ell)` symbol operations), integral-matrix second backend, writhe obstruction | matching multiplicities after unit cancellation, residue diagnostic | 59 archive tests pass; braid integration passes |
| `09/` | `unknot_progress_20261007.zip` | `fastunknot` 0.3.0 (`09/fast/`, `integration/fastunknot-0.3.patch`) | proved performance improvements to the scan; article with eleven research questions | — | 69 archive tests pass; factor/sparse integration passes |
| `10/` | `unknot_component_entropy_20261007.zip` | standard-library kernel (`10/code/`) | component-quotient factorization of F2 cobordism composition, `poly(w)·2^(w/2)` composition | sparse-profile restart potential (conditional) | 15 kernel tests pass; 453,611 production algebra comparisons agree |
| `11/` | `unknot_twist_research_bundle.zip` | `twistkh` (opt-in backend) | twist-compressed Khovanov complex for braid closures given as twist blocks, exact preflight cost certificates | — | 62 archive tests pass; opt-in twist backend integrated; 200 prior and 100 new production degree comparisons agree |
| `12/` | `unknot_frobenius_research.zip` | opt-in adapter for `fastunknot` (`12/reference/legacy/` baseline) | exact component quotient for compiled cobordisms, succinct block cancellation | quasi-polynomial bound for the structured block problem only | 29 archive tests; opt-in component contraction integrated; 229 production tests pass |
| `13/` | `unknot_research_20261007.zip` | implementations for `fastunknot` | homological windows (any prescribed interval of unreduced Khovanov homology over F2), finite nilpotent reduction | quasi-polynomial bound for prescribed homological queries under diagram parameters | 64 scanner and 10 hierarchy tests pass; exact windows integrated |
| `14/` | `unknot_continuation_quotients.zip` | `fastunknot` 0.4.0 | interval normalization, length-two continuation quotients, certified scalar Fitting splitting | exact window ordering | 94 archive tests pass; intervals and graded scalar splitting integrated |
| `15/` | `unknot_radical_transfer_20261007.zip` | survivor-first compression code | sharp radical nilpotence index 2k of the characteristic-two arc category, two-pass transfer | — | 18 archive tests and independent certificates pass; survivor prediction and adaptive shortcut integrated |
| `16/` | `unknot_recognition_dense_algebra_20261008.zip` | dense cobordism-algebra code | `poly(m)·2^m` dense coefficient algorithm by ranked subset convolution, certified finite-quotient filters | — | 74 archive tests and independent algebra checks pass; homogeneous coefficient path integrated |
| `17/` | `unknot_potts_frontiers.zip` | `fastunknot` with opt-in Potts backends (`17/fast/`, `integration/changes.patch`) | fixed-color Potts transfer for an exact Jones specialization, single-exponential in a Tait-graph frontier at most half the cut-edge frontier; component-factored transfer | — | 172 archive tests and independent cube audit pass; exact Potts options integrated |
| `18/` | `unknot_twist_research_2026-10-08.zip` | additive continuation of `fastunknot` (`18/fast/`, `integration.patch`) | exact long-twist recurrence for reduced F2 Khovanov homology, streamed homology backend, direct braid-profile structural evaluation | — | not run |
| `19/` | `unknot_rank_two_kernels_20261007.zip` | standard-library rank-two braid kernel (`19/src/`) | optimal one-pass disjoint rank-two substitutions in `O(n log n)`, linear replay verifier | quasi-polynomial bound for flat rank-two inflations of `O(log² n)`-crossing cores only | 33 archive tests and 16 real-upstream cases pass; bounded preprocessing integrated |
| `20/` | `ProveIt_Unknot_Extremal_Windows_2026-10-07.zip` | standard-library `unknot_windows` with an upstream adapter (`20/integration/`) | exact low-degree and mirror Khovanov windows with a one-degree halo, three-outcome probes, nice-order certificates | `n^O(log n)` for windows of depth `O(log n)` at girth `O(log² n)` | 14 archive tests and 393-window audit pass; optional minimal windows integrated |
| `21/` | `unknot_disk_frontier_research.zip` | standard-library disk-frontier kernel (`21/src/`) with a guarded `FastScan` adapter | common-disk certificates from the rotation system, ear-insertion orders, minimal complex with adjacent-degree maps | `poly(n,1+R)·2^O(B)` for certified explicit scans | not run |

Archives `01/`–`06/` each contain a README, a LaTeX report with PDF under
`docs/`, examples, recorded results, and a standard-library-only Python package.

`07/`–`12/` were placed on 7 October 2026. Each is a research continuation of
this project, and all but `10/` extend or patch `../fast/`. Report `07/` and the factorization, sparse elimination, and resource handling
from `09/`, plus the braid specialization from `08/` and opt-in component contraction
from `12/`, and twist compression from `11/` are integrated
(315 current production tests pass). Local reruns of
`08/`, `09/`, `10/`, and `11/` passed 59, 69, 15, and 62 test methods respectively.
They were originally placed as delivered under the intake rule; this later
algorithm-improvement task performs review and integration separately. The
delivered archive files remain unchanged. Their recorded results are the authors' own. `08/` ships its changed files in the repository's own
layout (`08/Topology/UnknotRecognition/...`); `11/` suggests
`research/twist_compression/` as its home. Both are kept inside their report
directories as delivered.

`13/`–`16/` were placed as delivered on 7 October 2026 under the intake rule:
no test runs, no patch application, no review. Text files are stored with LF,
and checksum files are dropped. Their recorded results are the authors' own.

`17/`–`21/` were placed the same way on 7 October 2026. `17/` and `18/` each
ship a patch against `../fast/` and a pinned copy of the project under
`reference/`; neither patch is applied. `18/` suggests
`research/twist-continuation-20261008/` as its home; it is kept here as
delivered.

Separately from placement, the algorithm-improvement task reviewed `15/` and
`16/` in isolated archive extractions. Their source files remain unchanged.
The current implementation integrates the survivor/degree-gap shortcut from
`15/`, with adaptive switching, and homogeneous coefficient multiplication
from `16/`, with a further top-degree shortcut. The full transfer engine and
finite-quotient filter are not integrated. Current validation passes 277 tests;
local logs, proofs, applicability limits, and paired measurements are in
`../synthesis/radical.tex` and `../synthesis/homogeneous.tex`. Report `13/` contributes the integrated exact window scanner and mirror bound;
`../synthesis/windows.tex` describes the new bounded adaptive widening policy.
Its 64 scanner and 10 hierarchy tests pass. Report `14/` passes 94 tests;
interval normalization, decision quotients, and scalar splitting are now optional
production backends. Scalar changes preserve recovered quantum shifts by default.
See `../synthesis/continuations.tex` for the sharper conditional checkpoint bound,
267-test integration, independent finite algebra verification, and negative timing
results. Its separate order optimizer remains unintegrated. Archive source files
are unchanged.

`07/` continues the project's own `../fast/` package
rather than being an independent implementation. It contains:

- the article (`paper/`);
- the modified package (`fast/`);
- the baseline it was made from (`reference/fast/`, pinned to ProveIt
  `4e6fe879e`);
- `integration.patch`, benchmarks and provenance.

The archive was originally placed as delivered, without review. On 7 October
2026, the continuing algorithm-improvement task reviewed and integrated its
patch into `../fast/`; all 69 integrated tests passed on CPython 3.13.14. The
archive remains unchanged. The authors' archived timings remain separate from
the new local measurements in `../fast/results/structural_integration_20261007.json`.
See `../synthesis/structural.tex` for the integration analysis and proof limits.

Dated note (2026-10-07): the SHA-256 manifests `01/MANIFEST.sha256`, `06/MANIFEST.sha256` and `12/checksums.sha256`, and those of `../proposals/01`–`03`, were removed at Vladimir's direction (imported reports keep no SHA-256 records; the files they listed are unchanged, and the bytes remain in Git history). Reports placed later keep no checksum files.

## Test status (last observed 18 September 2026)

All six suites pass on CPython 3.14.4 / Windows 11 with exactly the test
counts in the table above (`python -m unittest discover -s tests` from the
archive directory; each suite takes 1–4 s). The archives themselves recorded
CPython 3.13.5 on Linux. No archive source file was modified.

Longer runs shipped with the archives, which were **not** repeated here:
`01/tools/validate_exhaustive.py` (all grids of size ≤ 6; the archive
reports about 3 s for size 6, and warns that size 7 has millions of grids),
`05/scripts/experiments.py` (682 two-strand braids; about 25 s recorded), and
each archive's `benchmark.py` / `reproduce.py` / `run_validation.py` (seconds).
The archives' own recorded outputs are in their `results/`, `validation/` and
`docs/` directories. All six reports state that the requested
`n^O(log n)` implementation was not achieved and explain why; the synthesized
review of them is `../synthesis/report.pdf`.

Cross-validation of the archives against each other (five Khovanov
implementations, six pattern testers, the grid search of `01/` against the
Khovanov homology of `04/`) is in `../synthesis/data/`.

### Subsequent incoming rank-two review

The algorithm-improvement task separately reviewed
`docs/incoming/unknot_rank_two_kernels_20261007.zip` from commit `d569a29de`
in a scratch extraction. All 33 archive tests and its formerly unrun 16-case
real-upstream gateway smoke test pass. The production tree now includes its
optimizer and independent verifier with an optional bounded recognition stage;
272 integrated tests pass. The source archive is preserved unchanged. Proofs,
conditional complexity, barriers, and end-to-end measurements are maintained in
`../synthesis/ranktwo.tex`. The simultaneously received Potts-frontier and newer
twist archives remain queued for mathematical and integration review.

The later `docs/incoming/ProveIt_Unknot_Extremal_Windows_2026-10-07.zip` was
reviewed in a scratch extraction, preserving the delivered archive. Its 14 tests
and independent audit (393 windows, 1772 certified stages, 15 padding cases)
pass. The production integration targets current `FastScan`, rather than the
archive's untested older adapter. The new optional minimal-window strategy,
geometric certificate, stronger conditional bounds, and negative timings are
in `../synthesis/extremal.tex`; all 277 production tests pass. The recently
arrived disk-frontier report remains unreviewed.

Reports `19/` and `20/` were reviewed in scratch extractions before their
numbered placement reached this branch. Their placed Python sources match
those reviewed copies. The placement instruction itself involved no review;
these later test and integration results belong to the continuing algorithm task.

Report `17/` has since been reviewed under the algorithm-improvement task:
172 archive tests passed without modifying the archive, and the independent
smoothing-cube audit passed against the integrated code. Its optional Potts
filters and exact component transfer are integrated into `../fast/`; the
ring-valued Fitting proposals remain research material. This later review
is separate from the original as-delivered placement.
