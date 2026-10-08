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
| `12/` | `unknot_frobenius_research.zip` | opt-in adapter for `fastunknot` (`12/reference/legacy/` baseline) | exact component quotient for compiled cobordisms, succinct block cancellation | quasi-polynomial bound for the structured block problem only | 29 archive tests; opt-in component contraction integrated; 222 production tests pass |
| `13/` | `unknot_research_20261007.zip` | implementations for `fastunknot` | homological windows (any prescribed interval of unreduced Khovanov homology over F2), finite nilpotent reduction | quasi-polynomial bound for prescribed homological queries under diagram parameters | not run |
| `14/` | `unknot_continuation_quotients.zip` | `fastunknot` 0.4.0 | interval normalization, length-two continuation quotients, certified scalar Fitting splitting | exact window ordering | not run |
| `15/` | `unknot_radical_transfer_20261007.zip` | survivor-first compression code | sharp radical nilpotence index 2k of the characteristic-two arc category, two-pass transfer | — | not run |
| `16/` | `unknot_recognition_dense_algebra_20261008.zip` | dense cobordism-algebra code | `poly(m)·2^m` dense coefficient algorithm by ranked subset convolution, certified finite-quotient filters | — | not run |

Archives `01/`–`06/` each contain a README, a LaTeX report with PDF under
`docs/`, examples, recorded results, and a standard-library-only Python package.

`07/`–`12/` were placed on 7 October 2026. Each is a research continuation of
this project, and all but `10/` extend or patch `../fast/`. Report `07/` and the factorization, sparse elimination, and resource handling
from `09/`, plus the braid specialization from `08/` and opt-in component contraction
from `12/`, and twist compression from `11/` are integrated
(222 current production tests pass). Local reruns of
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
