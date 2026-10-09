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
| `18/` | `unknot_twist_research_2026-10-08.zip` | additive continuation of `fastunknot` (`18/fast/`, `integration.patch`) | exact long-twist recurrence for reduced F2 Khovanov homology, streamed homology backend, direct braid-profile structural evaluation | — | 254 archive tests and independent recurrence/slope audits pass; additive RLE frontend and optional source profile integrated |
| `19/` | `unknot_rank_two_kernels_20261007.zip` | standard-library rank-two braid kernel (`19/src/`) | optimal one-pass disjoint rank-two substitutions in `O(n log n)`, linear replay verifier | quasi-polynomial bound for flat rank-two inflations of `O(log² n)`-crossing cores only | 33 archive tests and 16 real-upstream cases pass; bounded preprocessing integrated |
| `20/` | `ProveIt_Unknot_Extremal_Windows_2026-10-07.zip` | standard-library `unknot_windows` with an upstream adapter (`20/integration/`) | exact low-degree and mirror Khovanov windows with a one-degree halo, three-outcome probes, nice-order certificates | `n^O(log n)` for windows of depth `O(log n)` at girth `O(log² n)` | 14 archive tests and 393-window audit pass; optional minimal windows integrated |
| `21/` | `unknot_disk_frontier_research.zip` | standard-library disk-frontier kernel (`21/src/`) with a guarded `FastScan` adapter | common-disk certificates from the rotation system, ear-insertion orders, minimal complex with adjacent-degree maps | `poly(n,1+R)·2^O(B)` for certified explicit scans | 52 archive tests, pinned-source audit and 14,658-state geometry audit pass; optional adaptive full transfer integrated |
| `22/` | `unknot_arithmetic_continuations.zip` | `fastunknot` continuation (`22/fast/`, integration patch under `22/integration/`) | supplied-Montesinos `UNKNOT`/`KNOTTED` classifier, checked local obstructions from non-embeddable Montesinos disk tangles, linear-bit slope arithmetic | — | 152 archive tests and independent arithmetic/local audits pass; checked-source classifier and opt-in local wrapper integrated |
| `23/` | `ProveIt_UnknotRecognition_SymbolicCompression_2026-10-08.zip` | implementation and patch for `fastunknot` (`23/implementation/`, `23/patches/`) | exact graded transfer, exact finite twist tails from the cap `L+2`, succinct structural certificates on binary run input | quasi-polynomial event count under a conditional dependency-graph hypothesis | 281 archive tests pass; graded transfer and exact symbolic transport integrated; earlier rank law and conditional repair bound reviewed |
| `24/` | `unknot_compression_kernels_2026-10-08.zip` | `fastunknot` with scanner patch (`24/fast/`, `24/integration/`) and `dihedral_covers` | three-record classification of dihedral surface covers, bidirectional survivor transfer with exact pruning | — | 268 archive tests pass; corridor transfer and sparse scalar setup integrated; surface-cover kernel and ordered-point queries maintained separately, 534-test checkpoint |
| `25/` | `unknot_cyclic_garside_20261007.zip` | exact cyclic Garside compressor and independent replay (`25/cyclic_garside/`) | shared prefix/target arithmetic, fixed-radius interval optimization, certified source-braid portfolio | quasi-polynomial recognition for a proved class of inflated small braid cores | 45 file hashes verified; all 47 delivered tests and upstream adapter smoke pass; bounded source probe integrated, 517-test integration checkpoint |
| `26/` | `ProveIt_Unknot_Determinant_Continuations_2026-10-07.zip` | marked residue-four observer and singular-safe terminal kernel (`26/detshadow/`) | quantum recovery, exact marked continuation norm, bordered determinant queries, critical square law | conditional `poly(n,R) 2^O(W)` stopping-prefix bound | 35 delivered and 560 maintained tests pass; optional marked observer integrated; 4,503 geometric completion queries audited; terminal reuse remains a research prototype |
| `27/` | `ProveIt_Report25_Causal_R3_2026-10-07.zip` | local rewrite prototype and RIII adapter (`27/prototype/`, `27/integration/`) | canonical initial births followed by accumulated-support search | conditional `N^(b+O(1)) (Ck)^k` unlocking bound | 42 delivered hashes and pinned simplifier verified; corrected replay and guarded inverse pruning integrated with optional clustered/adaptive search; 550 production tests pass; actual-diagram audit does not support changing the default |
| `28/` | `unknot_classical_closure_research_20261007.zip` | closure-rank compression and reset driver (`28/src/closure_reset/`) | scalar/total-linear first jet, pure block bounds, geometric single-survivor resets | conditional `poly(n) 2^O(g)` bound in actual reset gap | 29 delivered tests and 160-diagram audit pass against current production; optional closure backend integrated, 567 tests pass; one source pin mismatches its stated revision; expanded 624-scan discovery finds no nonsingleton block |
| `29/` | `unknot_modular_boundary_2026-10-08.zip` | optional finite-field backend and patches (`29/patches/`) | modular marked-continuation Euler observer, checked suffix boundary responses reused across completed matchings | — | not run |
| `30/` | `unknot_recognition_research_20261008.zip` | `fastunknot` continuation (`30/fast/`, `integration.patch`) | exact binary boundary tensors, three compression kernels with compressed transport | — | not run |
| `31/` | `unknot_certified_primitives_20261008.zip` | certified primitives with integration material (`31/integration/`) | exact cocycle-span transshipment and source-normal candidates; other delivered primitives retain their separate integration records | polynomial span optimization, not genus minimization | cocycle portion integrated with native primitive discovery, Dijkstra flow and independent source-disc replay; 507 hashes and 15 delivered cocycle tests pass |
| `32/` | `unknot_graded_torus_20261008.zip` | graded scanner (`32/src/`, `32/integration/`) | local cancellation bound by absolute homological-quantum bidegree occupancy, four-strand torus-block scanning | — | not run |
| `33/` | `proveit_unknot_causal_kernels_2026-10-08.zip` | causal-kernel code (`33/src/`) | deterministic `poly(N,k)·2^O(k)` decision whether at most `k` RIII moves expose a crossing-decreasing RI or RII | — | not run |
| `34/` | `ProveIt_Unknot_Braid_Kernel_2026-10-08.zip` | `braidkernel` package (`34/braidkernel/`, `34/integration/`) | certified braid kernels and linear Markov descent | — | not run |
| `35/` | `unknot_projectors_and_seams_20261008.zip` | optional primary backend with integration material (`35/source/`, `35/integration/`) | polynomial-projector extension of scalar Fitting splitting via the Frobenius fixed algebra; exact full-boundary assembly of dihedral surface covers with binary sheet counts | — | not run |
| `36/` | `unknot_research_20261008.zip` | `fastunknot` modules under `36/Topology/` and `integration.patch` | arithmetic-progression certificates for compressed overlaps, congruence families for regular-cover gluings, checked primitive extreme normal disks | — | not run |
| `37/` | `unknot_separator_research_20261008.zip` | reference implementation (`37/code/`) | first-hit factorization through vertex cuts, greedy rank budget giving the cut homology lower bound | — | not run |
| `38/` | `unknot_presentations_and_early_certificates.zip` | integration patch and project snapshot (`38/integration/`, `38/snapshot/`) | presentation-complexity bounds for knot groups, early first-jet certificates, streaming boundary responses | — | not run |
| `39/` | `unknot_su2_degree_budget_20261008.zip` | `su2budget` package (`39/code/`) | degree-budgeted SU(2) feasibility reduction; polynomial two-meridian traceless test on compressed presentations | — | not run |
| `40/` | `unknot_port_register_20261008.zip` | research backend (`40/src/`, `40/integration/`) | singular-safe port compression: exact F_2 homology of template-plus-low-rank differentials with finite-state multiplicity registers | — | not run |
| `41/` | `unknot_integral_shears_20261008.zip` | `shear_kernel` package with integration material (`41/shear_kernel/`, `41/integration/`) | integral tension kernels: exact minimum-length integral shears by capacity-scaling circulation, with an independent primal-dual verifier | — | not run |
| `42/` | `unknot_affine_families_20261008.zip` | source changes and patches (`42/source/`, `42/patches/`) | affine families and inherited structure: three exact improvements with a claim ledger | — | not run |
| `43/` | `unknot_whitehead_exposure_20261008.zip` | opt-in package with integration notes (`43/src/`, `43/integration/`) | certified Whitehead exposure beyond length descent | — | not run |
| `44/` | `unknot_dynamic_terminal_20261008.zip` | terminal-update code (`44/terminal_updates/`, `44/integration/`) | rank-two terminal contractions of anchored partitions; singularity-safe modular observers | — | not run |
| `45/` | `unknot_christoffel_20261008.zip` | code with integration material (`45/code/`, `45/integration/`) | compressed Christoffel width; exact compressed primitive-power test and torsion-free elimination | — | 22 delivery tests and saved examples reproduced; native rank-two terminal, disjoint projections and unit-coordinate forest extension integrated; 29,540-word and 80-diagram audits, shared candidate planning and bounded-run normalization with independent replay and uniform-subtree shortcuts; general acyclic elimination extension with adaptive fallback, 1,008 maintained tests pass |
| `46/` | `ProveIt_Unknot_Quotient_Kernels_20261008.zip` | repository overlay and `integration.patch` (`46/repo_overlay/`) | exact quotient kernels: three local improvements with whole-query measurements | — | orbit/topology and worker subset integrated; 805 maintained tests pass; full overlay not rerun |
| `47/` | `unknot_native_orbits_20261008.zip` | source snapshot and integration patch (`47/snapshot/`) | native normal-orbit research with an article, raw data and representative certificates | — | orbit replay and shared incidence integrated; 831 maintained tests pass; native-disc adapter and seed search pending |
| `48/` | `ProveIt_compressed_braid_certificates_2026-10-08.zip` | standard-library `compressed_b3` (`48/compressed_b3/`, integration notes in `48/integration/`) | native compressed three-braid recognition on binary straight-line programs, replayable certificates, singleton connected-sum forests with `INCONCLUSIVE` for unsupported wider leaves | conditional exceptional-minority bound | already integrated before numbered placement; 53 manifest files reconciled; prior 42 delivery tests and actual-kernel audit pass |
| `49/` | `unknot_source_anchored_20261008.zip` | standalone exact Python kernel (`49/src/`) with independent arithmetic replay | source-anchored primitive projections; saturated-lattice exponent bound `(t-1)^((t-1)/2) L^(t-1)` within a raw epoch, polynomial raw-epoch cost | polynomial raw epochs only; exposure, normalization and source resets stay open | 38 delivery tests and source-anchored arithmetic audit pass; native updater pin matches; polynomial raw-epoch theorem incorporated; native mixed-block lazy checker and producer integrated; general source-reset bound open |
| `50/` | `unknot_sparse_incidence_20261008.zip` | three additive modules, tests and `integration.patch` (adapted into `fast/`) | polynomial sparse component-incidence histogram for interval-pairing systems, O(s*r) subset-sum queries, certificates with zero witnesses | polynomial support via the existing weighted Agol–Hass–Thurston theorem | native sparse unsigned/signed APIs and independent replay integrated; 25 focused tests, 512 dense/sparse comparisons and all 1,050 maintained tests pass |
| `51/` | `unknot_singleton_dag_20261009.zip` | `integration.patch` and `repo_overlay/` (not applied), snapshots, independent certificate checkers | simultaneous Tietze elimination of acyclic singleton definitions with linear shared-grammar growth; 28-page article | local exact operation only; no whole-recognizer gain on the ordinary workload | linear grammar theorem incorporated; ordered checker adapted with legacy fallback and virtual inverses; 1,090 maintained tests, 1,600 old/new compressed abstract replays and 1,048 source replays pass; original search-policy overlay not applied |
| `52/` | `unknot_sparse_incidence_research_20261008.zip` | standard-library package (`52/src/`), vendored baseline, integration notes | sparse-zeta extraction of component/port signatures, balanced block deletion, independently certified sparse answers; 25-page article | polynomial bit complexity of the supplied incidence query, via weighted AHT | 33 delivery tests and 1,000 ordinary/signed graph audit cases pass; sparse-zeta theory reviewed; native integration pending |
| `53/` | `proveit_weighted_normal_components_20261009.zip` | six additive runtime modules adapted into `fast/`, tests, examples, `reproduce.py` | weighted normal components and quadrilateral disc-count reduction: component weights without expansion, essential disc counts from three statistics, independent weighted replay; 30-page article | local reduction; a positive count is an unknot witness only once the triangulation is bound to the knot exterior | native weighted census and quadrilateral core integrated with independent replay; all 1,084 maintained tests and 5,100 native Regina comparisons/replays pass; diagram provenance and candidate discovery remain open |

Archives `01/`–`06/` each contain a README, a LaTeX report with PDF under
`docs/`, examples, recorded results, and a standard-library-only Python package.

`07/`–`12/` were placed on 7 October 2026. Each is a research continuation of
this project, and all but `10/` extend or patch `../fast/`. Report `07/` and the factorization, sparse elimination, and resource handling
from `09/`, plus the braid specialization from `08/` and opt-in component contraction
from `12/`, and twist compression from `11/` are integrated
(431 production tests passed at that checkpoint). Local reruns of
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

`17/`–`24/` were placed the same way on 7 October 2026. `17/` and `18/` each
ship a patch against `../fast/` and a pinned copy of the project under
`reference/`; neither patch is applied. `18/` suggests
`research/twist-continuation-20261008/` as its home; it is kept here as
delivered.

`35/`–`48/` were placed the same way on 8 October 2026, numbered by arrival
commit (`36/` before `37/` within one commit, by member times). `48/`
arrived in the same commit as `47/` (`36f1dd8ef`) but was placed later.
Their checksum files are dropped; the delivered self-check scripts that read
them (`35/scripts/reproduce.py`, `36/verify_release.py`,
`37/code/check_manifest.py`, `40/scripts/checksums.py`,
`42/scripts/check_hashes.py`, `44/scripts/verify_manifest.py`,
`45/verify_manifest.py`, `46/verify_package.py`, `47/verify_bundle.py`,
`48/experiments/verify_manifest.py`) therefore report the manifest absent.
`47/` later had its manifests restored (`dd54dd927`).
`37/results/benchmark_medians.csv` is stored with LF. Each delivery states
that it does not prove general quasi-polynomial recognition.

`49/`–`53/` arrived together in drop commit `2c7f4fd68` (9 October 2026) and
were placed the same way, numbered by member timestamps (ties by archive
name). `50/` and `52/` are different deliveries whose archives share the
wrapper name `unknot_sparse_incidence_20261008/`. Their checksum lists
(`SHA256SUMS`, `MANIFEST.sha256`, `CHECKSUMS.sha256`) verified clean and were
dropped; `50/tools/check_manifest.py`, `51/scripts/verify_bundle.py` and
`53/reproduce.py verify-manifest` therefore report them absent. `53/`, whose
generic archive name hid it, was placed in a second pass. `51/MANIFEST.json` and `53/MANIFEST.json` carry
provenance beyond hashes (baseline commit, titles, roles) and are kept. Delivered text files
were CRLF and are stored with LF; ignored run records (`*.log`, `*.bbl`) are
force-added as delivered.

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
twist archives were queued at that checkpoint; their subsequent reviews appear below.

The later `docs/incoming/ProveIt_Unknot_Extremal_Windows_2026-10-07.zip` was
reviewed in a scratch extraction, preserving the delivered archive. Its 14 tests
and independent audit (393 windows, 1772 certified stages, 15 padding cases)
pass. The production integration targets current `FastScan`, rather than the
archive's untested older adapter. The new optional minimal-window strategy,
geometric certificate, stronger conditional bounds, and negative timings are
in `../synthesis/extremal.tex`; that checkpoint passed all 277 production tests.
The subsequent disk-frontier review is documented below.

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

Report `21/` was subsequently reviewed separately from placement. Its 52 tests
pass unchanged, and the previously unperformed scoped AST audit agrees with
the three pinned Git blobs. Production now has an optional disk-certified full
transfer after adaptive sparse/residue shortcuts, with transactional fallback.
The independent geometric and chain-certificate rerun is in `../synthesis/data/`;
performance scope and the raw-width obstruction are in `../synthesis/disk_transfer.tex`.

Report `18/` has now been reviewed under the continuing algorithm task. Its
254 tests pass unchanged; the production macro core differs from the pinned
copy only by a trailing blank line. The additive recurrence/streaming APIs,
RLE frontend and optional source-word profile are integrated, with additional
shared-deadline and mutable-budget checks. Independent recurrence, cube and
turnback audits were rerun against production; article and measurement scope
are in `../synthesis/twist_continuation.tex`. The delivered report is unchanged.


Report `22/` has now been reviewed under the continuing algorithm task.
All 152 delivered tests pass unchanged; production adds its checked Montesinos
source classifier and separate local-obstruction wrapper, with final-verification
deadline and option validation regressions. All 411 maintained tests pass.
The 1,200-source, local-map, 21-checkpoint and 1,398,101-entry identity audits
were rerun against production. Scope, proofs and paired measurements are
maintained in `../synthesis/rational.tex`; the delivered archive is unchanged.
The patch and all 81 patched-file hashes match the delivered manifest, and
82 source Git blobs match the pinned commit. The package-wide checksum script
cannot run because this delivered tree lacks its `SHA256SUMS`; this narrower
validation scope is retained in `../synthesis/data/rational-source-audit.json`.


Report `23/` is partially integrated: the full quantum-ordered transfer and
adaptive scanner policies are now in production, with transactional installation
and additional deadline checks. All 281 archive and 426 maintained tests pass;
1,812 full stage contractions and 114 pinned-source blobs were checked.
The symbolic signed-run frontend, earlier tail-rank threshold and repair-DAG
proposals retain separate review obligations. Theory and measurement scope are
in `../synthesis/graded_transfer.tex`; the delivered report is unchanged.


The remaining report `23/` review is complete: its exact hexadecimal interface
and independent structural replay were adapted into the existing run frontend.
The earlier total-rank law was checked on 392 explicit complexes and is recorded
without reducing the full-profile cap. The 380-fixture repair-DAG check supports
a conditional accounting theorem, not an implemented knot-exterior hierarchy.
All 431 maintained tests pass; `../synthesis/symbolic_runs.tex` states the scope.


Report `24/` has its scanner contribution integrated: full survivor-corridor
transfer, per-component direction choice, an adaptive sparse-work allowance,
and direct sparse-scalar/Boolean-port controls. All 458 maintained tests pass.
The archive wrapper verifies 20 integration-manifest hashes and passes its 268
scanner tests, surface-cover suite and deterministic audits in a temporary copy.
The advertised full `SHA256_MANIFEST.json` is absent; no broader hash claim is
made. Production repeats 3,885 entrywise comparisons over 555 prefixes, all
555 full contraction certificates, and support and representation audits.
Proofs, measurements, and resource semantics are in
`../synthesis/corridor_transfer.tex`. The separate dihedral-cover kernel review
is now complete and its maintained derivative adds binary JSON, cooperative
checks and exact ordered-point component comparison. The full checkpoint passes
534 tests; 196,712 marked comparisons against literal equivariant bijections
supplement the 13,846 expanded-topology checks. `../synthesis/surface_covers.tex`
gives the proofs and the two-mark obstruction to a constant state-type bound.
The geometry module requires a supplied presentation and is not a knot certificate;
extracting it from an exterior and representing full attaching maps remain open.


Report `25/` was extracted from `docs/incoming/unknot_cyclic_garside_20261007.zip`
without altering its delivered files. All 45 manifest hashes and six inspected
source Git blobs were verified (three tied to the pinned path/commit; three
recorded by exact blob only). Its 47 tests and previously unexecuted adapter
smoke pass against this checkout. Its maintained derivative now supplies an
optional independently replayed source-braid probe with shared local/global
checks and complete fallback. The modular Alexander obstruction precedes the probe, and an inconclusive result
is reused on an unchanged diagram. Jones follows the probe so that compression
can avoid its cost on a larger diagram. The integration checkpoint passed all 517
production tests; isolated-compressor and complete-recognition measurements
are retained separately. The theory, fixed-radius complexity bound, restricted
small-core theorem and limitations are in `../synthesis/cyclic_garside.tex`.
The checksum-only `SHA256SUMS.txt`, temporarily tracked at the integration
checkpoint, is now omitted under the intake policy. Its 45 verified entries
remain recorded in the source audit; the original archive is recoverable from
arrival commit `09c9cfe4b`. The non-manifest delivered files remain unchanged.


Reports `26/`--`28/` are numbered in arrival order (`a58110851`, `3990b5c80`,
`8f5820a52`). The title "Report 25" inside `27/` is the supplier's numbering;
it does not replace this collection's earlier Garside report. Each single
wrapper was removed, and checksum-only files were verified in scratch and
omitted: `26/MANIFEST.sha256`, `27/SHA256_MANIFEST.txt`, `28/SHA256SUMS`.
Delivered instructions referring to them require recovery of the original
archive from its arrival commit. Only `28/results/benchmarks.csv` required
CRLF-to-LF normalization. All other placed bytes match delivery.
The intake and source-pin audit is retained in
`../synthesis/data/incoming-26-28-source-audit.json`; unit-test logs are separate.
The archives have been retired from the drop zone under its documented policy,
including the previously placed Garside archive after verification against its
placement commit. No delivered code, article or data is replaced by maintained
integration work.

Report `28/` is reviewed in `../synthesis/closure_resets.tex`. Its optional
maintained backend checks whole single-matching components and the actual
classical suffix closure before rank-preserving resets. A local work limit
falls back to the same saturated scan. The stated geometry pin does not match
that path at the named inspected revision (the other three do); its retained
geometry fixture omits four composition fast paths. The corrected audit is
`../synthesis/data/closure-reset-source-audit.json`. The earlier intake ledger
already marked this path mismatch; its summary and catalog wording overstated
the verification and are now corrected. No delivered
source, article or provenance record has been rewritten. The maintained
tests and source-pinned discovery results are separate evidence.

Report `26/` is reviewed in `../synthesis/determinant_continuations.tex`.
The maintained `shadow` backend evaluates actual marked completions with
interruptible integer determinants, retaining exact capped scanning when its
local budget expires. The original 701-diagram validation and a 176-scan
upstream probe pass. A separate checked common-Tait-graph producer agrees with
direct determinants on all 3,186 connected queries tested; 1,317 disconnected
queries have determinant specialization zero. Common-kernel reuse remains
outside production pending a maintained interruptible implementation and
amortization measurements on actual observer traces. The follow-up in
`../synthesis/boundary_reuse.tex` proves a cut-face-fragment producer with
boundary-only query checks, independently audits all 4,503 actual completions
and 3,468 arbitrary pairings, and measures isolated repeated-query gains.
The maintained Euler backend now adaptively reuses boundary path summaries;
all 572 integrated tests pass at that checkpoint. A subsequent implementation
factors actual completed signed Tait graphs at articulation vertices before
dense allocation (`../synthesis/tait_blocks.tex`), with 577 passing tests and
separate initial-query, raw-scan, and full-recognition benchmarks. The later
scheduler retains query-capped Euler observations after marked-work exhaustion
(`../synthesis/shadow_fallback.tex`); all 582 tests pass. The standard backend
remains the default.

Report `27/` is reviewed in `../synthesis/causal_r3.tex`. The maintained
implementation adds opt-in support-aware/adaptive RIII search, fixes ambiguous
crossing-only certificates, and restricts immediate-inverse pruning to moves
that added no support. Its actual-diagram audit finds no crossing-count gain
at the tested default bounds, so the historical search remains the default.
The delivered report and adapter remain unchanged.

Report `27/` retains three delivered trailing spaces in its recorded LaTeX/PDF
inspection logs. They are part of the archived evidence, not new formatting in
the maintained implementation. Executable script modes are preserved from ZIP.

The maintained continuation of report `17/` now includes certified separator
orders (`../synthesis/separator_orders.tex`) and an optional measured-work
Potts policy (`../synthesis/adaptive_potts.tex`). The former supplies a general
square-root crossing-frontier order; the latter defers its preparation, keeps
unchanged tables, and charges any restart to the original transition budget.
A logarithmic remaining tail has a polynomial work bound. These yield a
general subexponential fixed-color scalar query, not a general subexponential
recognizer. The 595-test checkpoint includes independent scalar comparisons,
while the benchmark retains initial-policy source, gains, regressions and
censored queries. The delivered report is unchanged.

Report `48/` is the identical delivery already integrated in the maintained
compressed-braid backend and reviewed in `../synthesis/compressed_braid.tex`.
The numbered placement was checked against the original archive and its prior
integration hashes: all 53 delivered files match. Its omitted `SHA256SUMS` has
been restored verbatim. See `../synthesis/data/report48-placement-audit.json`.
The prior 42 delivery tests, actual-kernel injection, exhaustive 87,381-word
audit and native integration remain recorded in `../synthesis/data/`; these
are previous executions, not new runs caused by relocation. Subsequent native
work adds independently verified wider-factor fallbacks, adaptive and lazy
factor preparation, and compact root permutations. Arbitrary diagram-to-grammar
construction with a general favorable complexity bound remains open.

Reports `49/`–`53/` were subsequently reviewed under the ongoing algorithm-improvement
task. Their delivered files are unchanged. See `../synthesis/incoming_2c7f.tex`
and `../synthesis/data/incoming-2c7f-*` for original-archive reconciliation,
rerun results, strengthened native bounds and the integration boundary.
Report 50's sparse observer and independent checker are now integrated in
the maintained package; see `../synthesis/sparse_incidence.tex`. Report 53's
weighted component census and quadrilateral disc-count core are also integrated;
see `../synthesis/weighted_components.tex` and its native audit/timing records.
Report 51's ordered singleton checker is adapted to the native schema with
legacy compatibility; see `../synthesis/ordered_batch.tex`. Report 49's lazy
monomial source state is now integrated in both native producer and checker;
see `../synthesis/anchored_producer.tex`. Report 52 remains an independent reference
implementation.

Three further archives arrived in commit `92efcbaed`. Their initial integrity
checks and standalone persistent-circuit tests are recorded in
`../synthesis/data/incoming-92ef-*`. The adaptive periodic-merger scheduler
from `unknot_component_certificates_20261009.zip` is now integrated into the
maintained AHT producer with unchanged complete certificates; see
`../synthesis/adaptive_merger.tex`. Its alternative weighted/profile overlay
is not applied over the newer native census and independent verifier. The
other two deliveries initially remained under review. Subsequent persistent
circuit and component-support integrations are recorded below; the alternative
weighted transport and sparse-incidence overlay are not adopted. Original archives are retained.

The persistent signed-circuit idea in
`ProveIt_UnknotRecognition_Research_2026-10-09.zip` is now adapted to the
maintained independent version-eight checker. Consecutive raw batches share
one circuit and export once; all 1,112 maintained tests pass. See
`../synthesis/persistent_replay.tex` for the whole-block polynomial bound,
source-bound compatibility audit and native measurements. Its subsequent
producer integration is now in `../synthesis/persistent_producer.tex`: exact
greedy discovery shares a private raw circuit across batches and exports once.
All 1,116 maintained tests pass; the 84-diagram audit preserves certificates
and positive coverage. The delivered prototype and original archive remain unchanged.

Commit `b365341b1` adds `ProveIt_Unknot_Sparse_Incidence_Research.zip` and
`unknot_power_conjugacy_20261008.zip`. Initial README/contract review and all
94 delivered checksum entries pass; see
`../synthesis/data/incoming-b365-initial-triage.json`. That is the historical
initial review. The sparse observer still overlaps the maintained implementation.
The power-conjugacy delivery's 24 tests have subsequently passed, and its
plain-power minor argument now has a maintained compressed detector and
independent source replay; see `../synthesis/power_pairs.tex` and
`../synthesis/data/power-pair-*`. The native knot-specific rule uses an
already source-established torsion-free premise to accept any nonzero minor.
All 1,121 maintained tests pass. The broader conjugacy graph, compressed
conjugator discovery and claimed graph-abstraction boundary remain outside
this integration. Delivered braid-audit and timing records are not native runs.

The component-profile chapter of the same research archive is now reviewed in
`../synthesis/compact_coordinates.tex`. Its fixed-support dimension argument
reduces the maintained full-coordinate census to positive quadrilaterals plus
positive source-minimum vertex anchors. Full vectors are reconstructed by
separate producer and checker algorithms. The proof of `H <= v + 2*q` distinct
component vectors, and `H <= v + q` for two-sided components, is included with
its sharp one-tetrahedron example. All 1,125 maintained tests pass; 1,275
Regina cases preserve the dense inventories, legacy replay and orbit proofs.
The archive's full-carrier weighted-run bound is now reviewed in
`../synthesis/suffix_folds.tex`. The native deleted-suffix operation has a
stronger sharp `+2` run bound. It retains its independent checker and now
restricts dense vector arithmetic to the receiving interval; the delivery's
shared producer/checker arithmetic is not adopted.

Report 49 now also supplies the representation behind native source-anchored
compressed replay. Consecutive primitive projections and unit-coordinate forests
are authenticated against immutable source roots and a private monomial image
table, then exported once. The independent literal verifier and all producer
code remain unchanged. See `../synthesis/anchored_replay.tex` for the whole-block
bound, 1,132-test validation, 768 source replays and separately scoped algebraic,
full-certificate and whole-recognition measurements. The 2–3× supplied-schedule
gains do not imply a general recognition speedup. Producer discovery was
subsequently integrated below; bounds across source resets remain open.

Native source-anchored **producer discovery** is now integrated as well. It
reuses the maintained greedy projection/forest selection and independently
evaluates source counts and height profiles. Exact singleton priority and
rank-two terminal boundaries are preserved. See
`../synthesis/anchored_producer.tex` for the producer's polynomial raw-block
cost, unchanged complete certificate traces, independent replay and measurements
that include automatic discovery. This supersedes the producer-pending status
of the earlier checker-only integration, without resolving general source resets.

The power-conjugacy report's **plain-power graph** is now adapted to the native
compressed producer and both independent source replayers. Version-ten witnesses
contain a spanning tree plus one signed-cycle contradiction or pure-power seed.
The producer uses rational potentials; the checker peels leaves and compares
cycle products. Components of three or more labels extend the older pair-minor
rule. See `../synthesis/power_components.tex` for the torsion-free proof, exact
graph-abstraction completeness statement, binary product-difference-one family,
1,142 maintained tests and 654 source replays. Ordinary coverage is unchanged;
conjugated-power graphs and automatic exposure remain separate open tasks.

The canonical diagram-to-exterior gap identified in the normal-surface reports
is now addressed by a native Weeks crossing-cell construction followed by a
finite convex subdivision. A separate integer-coordinate checker verifies
every face against the source PD. Pulling from a retained pole reduces the
result from `80*max(1,n)` to `20*max(1,n)` tetrahedra; the old subdivision
remains available and independently replayable. The result is accepted by
the maintained compact-manifold validator. This supplies
provenance for that canonical geometry; it does not authenticate arbitrary
supplied or simplified triangulations. See `../synthesis/diagram_exterior.tex`.
Complete normal-vector search and verified simplification remain open
integration tasks. The restricted candidate family below is now available;
the default recognition policy retains its existing behavior.

Report 31's **cocycle-span optimization** now operates on the native canonical
exterior. Exact tree-gauged cohomology yields a primitive integral cocycle;
half-integral local-height levels supply binary normal coordinates. The
native optimizer replaces repeated Bellman--Ford passes with reduced-cost
Dijkstra augmentations, stopping at the settled sink. A separate primal/dual
checker reconstructs coordinates from edge weights and proves the exact
minimum piece count. This does not minimize genus: the three-crossing unknot
`[1, 1, -1]` remains a recorded miss after optimization.

The optional `--normal-seed` stage tests the raw surface before optimizing,
shares its allowance with every positive replay, and falls back to the
existing exact recognizer on failure. Its native witness binds the exact
stage-input PD to the compact exterior and an independently checked essential
disc. See `../synthesis/cocycle_seeds.tex` for the local complexity theorem,
connectedness argument, actual five-crossing optimized success, source audit,
Regina controls and complete-operation timings. The delivery remains unchanged.

Primitive discovery now schedules sparse equations by support size and live
column incidence, retaining exact rational pivots and the previous primitive
sign. All 84 source seeds and 17 positive certificate hashes are preserved.
Complete preparation improves 1.34–2.22× on the measured larger inputs, while
the smallest case adds about 3% overhead and full-recognition calls show no
broad gain. See `../synthesis/cocycle_sparse.tex`; the conservative dense
cohomology bound remains cubic.

The native AHT component path now prunes disjoint periodic supports with an
overlap sweep and a bounded queue fallback, preserving complete proof traces.
Static-gap contraction uses one coverage scan and reuses rows when unchanged.
All 600 audited interval traces and 17 source certificates are preserved;
the maintained suite passes 1,171 tests. Complete recognition improves
1.17–2.11× on five inputs deliberately routed through the native stage.
See `../synthesis/orbit_support.tex` for the per-closure bound, explicit
disjoint-system improvement, remaining default-budget caps and measurement scope.

Once the unweighted certificate proves one orbit, weighted production and
independent verification now use total input mass instead of transporting
weights through every event. The old certificate format and contents remain
valid; multiple orbits still require full transport. All 300 weighted audit
certificates and 17 source proofs are preserved, and 1,175 tests pass.
Complete native-stage recognition improves 1.08–1.35× on the measured five
inputs. See `../synthesis/single_orbit_weights.tex` for the conditional linear
mass bound, multi-orbit counterexample, compatibility checks and timings.

Report 31's **connectedness theorem** now also removes orbit searches from
the restricted cocycle stage. A separate source-bound verifier checks the
primitive integral class after an independent tree gauge and either a zero
spanning tree or the minimum-span witness. It then uses Euler characteristic
to identify the connected orientable disc. Both new witnesses and historical
component certificates replay independently. All 148 fresh Regina controls
agree; the 84-source default-budget audit now has 18 positives, 65 completed
restricted misses and one cap. The 32-crossing stabilized circle newly fits
the budget, while Gordian still caps during optimization. See
`../synthesis/cocycle_connectivity.tex` for the full proof, a primitive
Euler-one trefoil counterexample to omitting connectedness, and timings.
All 1,181 tests pass. Complete recognition improves 1.46–8.70× on six
deliberately routed native-stage inputs; independent replay improves
1.94–2.98× on four positives. Ordinary corpus calls still finish before
attempting this stage, so those gains do not imply a default-portfolio gain.

The checked zero-tree construction now supports **alternative tree gauges**
without another cohomology solve. A four-trial deterministic prelude precedes
span optimization; extra requested trials follow an optimization miss. The
same independent certificate checker accepts every new positive. On the
84-source corpus, positive records rise from 18 to 23 with the default four
trials, or 24 with 24 trials, preserving all earlier positive hashes. All
1,187 tests pass and 205 fresh Regina controls agree. A parallel investigation
of minimum edge-intersection weight found no new discs in 58 old-stage misses
and was retained as research rather than added to the recognizer. See
`../synthesis/cocycle_trees.tex` for the construction, exact limitations and
complete-call performance, including unsuccessful-search overhead.

The maintained report-31 span optimizer now uses **adaptive blocking flows**
on its zero-reduced-cost residual graph, handing off to Dijkstra after two
poor blocks and restarting on later zero-distance evidence. Its independent
optimality checker is unchanged. All 500 abstract optima and 82 comparable
source vectors are preserved; the two formerly capped standalone source
optimizations now complete. The full shared-budget Gordian stage still caps.
All 1,192 tests pass and 76 fresh Regina controls agree. See
`../synthesis/cocycle_blocking.tex` for the residual invariant, worst-case
accounting, an equal-cost family with linear residual search, and measured
source gains alongside adverse arbitrary-input controls.

Report 31's matching dual now also gives an **exact optimal-face description**:
eight difference constraints per tetrahedron characterize all tied optima.
The optional native face search obtains two extrema per selected root by
nonnegative shortest paths and reuses the independent span/source verifiers.
Four roots add one seven-crossing native proof, but complete recognition is
slower on the measured new positive and misses, so the option defaults to
zero. All 1,197 tests pass and 787 Regina surface controls agree. The retained
same-matching examples include discs and annuli at the same piece minimum;
tie-breaking does not preserve topology. See `../synthesis/cocycle_face.tex`
for the proof, bounded-search limits, source coverage and adverse timings.

The connectedness/class certificate now also supports **primitive annulus
caps**: in a knot exterior, a primitive connected orientable Euler-zero
surface has exactly one essential boundary circle, and capping the other
gives a compressing disc. A new annulus schema preserves the stored surface's
zero disc count and leaves the surface/span inspectors unchanged. Default
four-tree native coverage becomes 24 positives; the optional 24-tree policy
reaches 27. All 1,204 tests pass and 796 Regina comparisons agree, including
two rejected trefoil adversaries. Complete calls improve 1.57–1.64× on three
early annuli, 1.48× over face search and 1.35× on a late-tree case; the new
seven-crossing proof plus replay is about 16% slower than the old fallback.
See `../synthesis/cocycle_annulus.tex` for the proof, boundary controls,
certificate semantics and measurement limits.

The subsequent optional planar-capping integration broadens the sufficient
surface criterion beyond nonnegative Euler characteristic. A connected
orientable planar surface with exactly one essential boundary circle gives
a compressing disc after its inessential circles are capped. Two compressed
boundary weights certify the required counts, with independent source,
basis and weighted-trace replay. The four-tree source policy improves from
24 to 25 positives and the 24-tree policy from 27 to 30. All 1,798 surveyed
surfaces and five selected witnesses agree with Regina and expanded boundary
controls; all 1,210 tests pass. Reusing geometry validated within each call
reduces redundant preparation. Final full-call timings show a 1.12x gain on
the earlier seven-boundary witness, near parity on the earlier raw witness,
and costs on added positives and misses, so planar discovery remains opt-in.
The synthesis article records the elementary proof, binary-size query,
initial source snapshots, final 493-file pins and both timing runs. This
extends certificate coverage without establishing a general recognition bound.

The next integration reuses one prepared geometry during cocycle candidate
construction and applies a height-based Euler prefilter to raw and optimized
candidates. Independent positive verifiers remain byte-identical. An 84-source,
four-policy comparison reproduces the published baseline and preserves every
completed result apart from total guard work; 1,798 cell counts agree with
coordinate reconstruction and Regina. All 1,214 tests pass. The nine-round
complete-call comparison gives 1.26–1.28x on optimized positives, 1.47–1.51x
on later tree positives and 1.89–2.00x on continuing misses, with about two
percent overhead on immediate positives. The article retains both timing
runs, A/A variation, all 496 source pins, and the unchanged coverage and
optional-stage defaults. No general recognition-complexity bound follows.
