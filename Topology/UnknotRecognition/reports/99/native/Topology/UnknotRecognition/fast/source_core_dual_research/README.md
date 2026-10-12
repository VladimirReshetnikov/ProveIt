# Source dual forests for normal-cut handlebody censuses

This extension targets ProveIt commit
`8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`.
It removes the native unconditional refusal of complementary cores containing
3-handles. It processes the authenticated supplied normal cut; it does not
discover a useful normal surface or issue a standalone knot verdict.

## Integration

Four new runtime modules provide the source cap-incidence compiler, rooted
forest reduction, independent replay, and the native boundary-kernel finish:

- `fastunknot/source_core_dual.py`
- `fastunknot/source_core_dual_verify.py`
- `fastunknot/normal_cut_dual.py`
- `fastunknot/normal_cut_dual_verify.py`

The existing `normal_cut_handlebodies` entry point calls `finish_dual_cut` only
where it previously returned `core_has_three_handles`. The call consumes the
parallelity packet already computed by that entry point. No weighted orbit
discovery is repeated. The existing verifier dispatches the new
`normal-cut-handlebodies-v6` schema to its independent checker; all earlier
schemas retain their existing paths. No new dependency is required by the
runtime or the focused tests. Regina is used only by the optional independent
audit and comparative benchmark.

The dual compiler takes **authenticated source geometry**. Its low-level
functions are not validators for arbitrary handle descriptions. In native
use, both source geometry and marked boundary packets are authenticated before
the final census is accepted. It reconstructs the two actual belt-cap
occurrences of every source 2-handle, including loops, rather than reading an
algebraic boundary matrix.

The retained 0/1 charts and port labels are used as abstract charts after
cancellation. The topological claim is relative to exposed bands, not a
homeomorphism fixing the entire embedded 0/1 submanifold pointwise. Native
ports come from strict interior-rank face strips or edge caps; the dual
cancellations use extreme edge gaps and vertex-link caps. Their interiors are
disjoint, and the cancellation collars can be chosen to preserve those bands.

## Reproduction

Run commands below from `Topology/UnknotRecognition/fast/` in the patched
repository. The full repository test suite also requires its existing
historical report fixtures.

```bash
python -m unittest discover -s tests -p test_source_core_dual.py -v
python -m source_core_dual_research.audit --output /tmp/source-dual-audit
python -m source_core_dual_research.source_parity_audit --output /tmp/source-parity-audit.json
python -m source_core_dual_research.benchmark_mobius --output /tmp/source-dual-benchmark --rounds 5
```

The corpus audit loads the original entry-point bytes directly from the
declared git revision and executes that baseline with unchanged native
dependencies. Its report records the baseline entry-point hash and corpus
hash. It saves all seven new positive source/certificate packets and invokes
Regina on those seven actual cuts. The new entry point leaves all cases without
3-handles on exactly their prior execution path.

The optional matrix experiments use the accompanying finite solver directory,
which contains `dual_forest_search.py` and `dual_forest_verify.py`. Replace
`SOLVER_DIR` below by its absolute path:

```bash
python -m source_core_dual_research.matrix_audit --output /tmp/matrix_audit.json --solver-dir SOLVER_DIR
python -m source_core_dual_research.audit_obstructions --matrix-audit /tmp/matrix_audit.json --solver-dir SOLVER_DIR --output /tmp/source-dual-obstructions
```

The source matrix is built after the current deterministic 0/1 spanning
forest. The finite boundary matrix additionally contains its real annular
gluing rows and its finite bundle-boundary columns. Permanently even omitted
genus columns are inert for unit peeling and are not expanded. The optional
finite solver does not change native dispatch.

## Evidence and precise outcomes

| Evidence | Meaning |
|---|---|
| `native_audit.json` | All 106 pinned corpus inputs, baseline comparison, preservation checks, independent census replays, seven independent Regina comparisons |
| `certificates/*.json` | Seven new positive packets, each with triangulation, coordinates, and complete v6 certificate |
| `matrix_audit.json` | Source matrices for all 106 cases; full finite boundary matrices and exact forest-search results for the ten cases containing 3-handles |
| `source_parity_audit.json` | Independent uncapped occurrence totals and dual-vertex parity on all 3,239 source columns, plus three supplementary sources with multiple interior vertices |
| `obstructions/*.json` | Three source-authenticated negative raw-kernel packets, including their finite solver problems and stopping witnesses |
| `obstructions/obstruction_audit.json` | Independent source/boundary authentication and matrix reconstruction for those three witnesses |
| `mobius_benchmark.json` | Individual randomized paired samples, environment versions, and timing decomposition |
| `mobius_benchmark.csv` | Compact table of the same benchmark medians |

The measured pinned baseline completes **85 of 106** censuses. The extension
completes **92 of 106**, preserving all 85 previous complete censuses exactly.
All 92 resulting certificates replay independently, and all seven new censuses
agree with Regina's actual cut followed by exact `recogniseHandlebody` on
every component. The older README count of 83 is stale for this pinned source;
the saved baseline bytes and hashes make the 85 figure reproducible.

The ten focused test methods pass. They include all-corpus cap-incidence
reconstruction using independent local edge representatives and signed
orientations, loops, multiple interior vertices up to 16, certificate
mutations, producer-disabled replay, binary serialization, callbacks and
operation caps, unchanged prior schemas, and a spherical-cut control that
correctly remains inconclusive. The pure-Python `stellar_torus(k)` generator
constructs an actual sequence of finite 1-to-4 subdivisions, giving `1+3k`
tetrahedra and `k` interior vertices; it requires no Regina installation.

## What the matrix audit establishes

For the original source matrices, 81 of 106 cases have maximum column row
support at most two: 12 have maximum zero, 7 have maximum one, and 62 have
maximum two. The other 25 have maximum three. Direct uncapped counting also
finds at most three original geometric occurrences per surviving source
1-handle in every corpus case.

The separate source-parity audit checks all 3,239 original source columns,
including the columns later removed by the primal forest. It finds zero
violations of the bound three or of even dual-vertex incidence modulo two.
The local cap oracle uses 78 orientation-reversed cycle representatives and
agrees with the runtime cap compiler. Of the 74 columns consisting of three
distinct unit entries, seven give a parallel pair plus a loop and 67 give
three loops. The original corpus has at most one interior vertex per source,
so three supplementary stellar sources with two, four, and eight interior
vertices explicitly exercise the remaining triangle case, giving 3, 9, and
25 such columns. Supplementary records are labelled separately from the 106
original cases. This checks the occurrence-level boundary-squared relation;
it does not replace geometric counts by exponent sums.

Among the ten cores containing 3-handles, seven meet the degree-two hypothesis,
and the polynomial finite solver succeeds on all seven. Exact stopping-set
search also succeeds on the remaining three **bare-core** matrices. This does
not imply the entire cuts are handlebodies: the annular gluing rows must still
be included.

Only four of those ten **full finite boundary matrices** satisfy the
degree-two hypothesis. Exact search succeeds on the same seven full cases
accepted by the new native branch. It certifies `NO_FOREST` for the other
three, with stopping witnesses consisting entirely of nondeletable annular
rows:

| Corpus case | Witness rows in the finite problem | Witness size |
|---|---|---:|
| `pilot/finite_figureEight_interior/0` | 26, 27, 28, 29, 30, 31, 32 | 7 |
| `interior_2_3/mixed` | 11, 12, 13, 14 | 4 |
| `finite_trefoil_interior/mixed` | 16 | 1 |

The obstruction audit independently authenticates each parallelity and
boundary packet, reconstructs its 0/1 forest using explicit partitions,
reconstructs annular curves with the independent geometric tracer, and
rebuilds the whole finite problem. Every listed witness has no column of
total one, and every row is unavailable for dual 2/3 deletion. Thus changing
the dual forest cannot make these **fixed raw finite boundary kernels**
completely eliminable. This is neither a non-handlebody certificate nor a
knottedness certificate; geometric curve normalization, other initial
forests, different disk systems, or stronger topological moves are outside
that negative conclusion.

## Complete supplied-cut benchmark

The benchmark fixes the four-tetrahedron interior-vertex torus and scales its
normal Mobius-band vector. Both paths receive the same source face pairing
and coordinate vector. Native time includes source processing, compressed
census production, the complete certificate, and independent replay. Regina
time includes conversion to Regina objects, actual cutting, component
triangulation, and exact component recognition. Each point uses five
randomized paired rounds after a checked warm-up; the seed is 20261012.
Version and platform information are saved in the JSON report.

| Copies | Expanded Regina tetrahedra | Native producer + replay (ms) | Regina complete query (ms) | Median paired Regina/native ratio |
|---:|---:|---:|---:|---:|
| 1 | 91 | 4.056 | 0.895 | 0.225 |
| 4 | 151 | 26.507 | 1.420 | 0.0528 |
| 16 | 391 | 27.514 | 3.014 | 0.1069 |
| 64 | 1,351 | 28.289 | 8.825 | 0.3169 |
| 256 | 5,191 | 40.501 | 42.282 | 1.044 |
| 1,024 | 20,551 | 35.723 | 169.545 | 4.824 |

The native method is slower on the small expanded instances, by about 19
times at four copies. At 256 copies the methods are close; at 1,024 copies the
measured native complete query is about 4.82 times faster. These are timings
of the stated supplied-cut operators, not of full unknot recognition, and no
global quasi-polynomial complexity conclusion follows. Separately, the
focused tests verify a `2^4096`-scaled input and its exact census of
`2^4095+1` solid-torus components without expanding any normal sheets.
