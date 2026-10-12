# Dual Forest Normalization and Constrained Cancellation for Compressed Unknot Hierarchies

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

**Start with [the article PDF](article/dual_forest_normalization.pdf).** Its complete LaTeX source is [dual_forest_normalization.tex](article/dual_forest_normalization.tex), with section files and bibliography alongside it. [REPRODUCE.md](REPRODUCE.md) gives the exact integration, verification and measurement commands.

This package proves and implements a useful local improvement toward compressed unknot hierarchies. It does **not** claim a complete quasi-polynomial unknot-recognition algorithm. The native operation takes an authenticated triangulation and normal vector and, when its sufficient criteria complete, certifies the cut's component genus census.

## Main results

### 1. Remove all native core 3-handles in polynomial encoded time

The native complementary core already records the geometric information needed for top-handle cancellation. A rooted dual graph has one vertex per 3-handle, one exposed-boundary root, and one edge per original core 2-handle. Its endpoints are actual belt-cap occurrences. A zero-weight source edge contributes its original endpoint pair; a positive-weight source edge contributes the two extreme gaps, each ending at exposed boundary.

Connectivity of the original source 1-skeleton proves root reachability for every admitted native source and normal vector. Any dual spanning tree specifies genuine 2/3-handle cancellations removing all 3-handles. The article proves retention of the current exposed 0/1-handle port charts and the surviving attaching maps to the abstract lower base. It does not claim that the whole embedded lower submanifold is fixed pointwise or that arbitrary extra marked curves are already transported.

The new graph stage uses O(t) structural work to produce a tree and O(t alpha(t)) to check it, with polynomial bit cost in t and normal-coordinate bit length. It never enumerates the normal sheets. The source graph is unchanged under positive scaling of the normal vector, or more generally within a fixed zero/nonzero source-edge-weight stratum.

### 2. Characterize and optimize the dual-tree choice

For a fixed lower 0/1 spanning forest, let A contain the unsigned occurrence counts of 2-handle rows on the remaining 1-handle columns. A stopping set is a nonempty row set whose total on each column is zero or at least two. Earlier incoming research proves that raw cancellation completes precisely when column-leaf peeling leaves no stopping set; this article credits and re-proves that criterion.

A dual tree succeeds exactly when it meets every stopping set of A. This yields complete obstruction-guided search with depth bounded by the number s of 3-handles and at most 1+w+...+w^s search nodes when each witness offers at most w eligible choices. Disjoint stopping sets whose eligible edge union has insufficient graphic rank give short negative certificates.

When every column containing a unit entry meets at most two rows, peeling is directed reachability. The unseeded source strongly connected components are the exact mandatory deletion groups. Graphic–partition matroid intersection finds an independent representative from every group, or a Rado rank obstruction, in polynomial time. The article includes direct proofs of both shortest-path augmentation and failed-search obstruction extraction. The family of peelable row sets itself is not a matroid; an explicit counterexample is included.

### 3. Isolate the remaining original native column type

Every original native 1-handle cocore comes from a region of a triangular face, so the total actual occurrence count in a column is at most three. Moreover, the dual edges with odd uncapped entries form an even-degree subgraph, by the handle-chain boundary identity. Thus the only original native shape beyond the polynomial theorem is (1,1,1), constrained to a triangle, a parallel pair plus a loop, or three loops.

These constraints concern original native relations. Added interface relations and arbitrary later slides require separate analysis. Parity must use actual uncapped counts: saturation at two preserves stopping decisions but changes odd counts of three.

## Measured native improvement

The exact baseline is ProveIt commit:

```text
8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4
```

| Observation | Result |
|---|---:|
| Baseline complete cut censuses | 85 / 106 |
| Complete censuses with this extension | 92 / 106 |
| Earlier complete censuses preserved exactly | 85 |
| Successful independent certificate replays | 92 |
| New censuses agreeing with Regina | 7 |
| Full repository regression suite | 1,688 tests passed |
| Additional standalone finite focused tests | 18 passed |
| Finite independent oracle comparisons | 33,995 passed |

The finite comparisons comprise 26,995 exhaustive cases and 7,000 seeded random cases. They are graph/matrix problems, not additional knot examples. The ten new native test methods are already included in the 1,688 repository tests.

All ten corpus cuts with 3-handles have solvable bare core matrices. After adding the authenticated finite interface relations, exactly seven are solvable by the fixed raw kernel. The other three have independently authenticated stopping sets consisting entirely of rows unavailable for top cancellation. No change of dual tree can resolve those fixed kernels. The saved negative packets make this an actionable research finding, without making any non-handlebody or knot verdict.

The source parity audit checks all 3,239 original columns in the 106 corpus cases, with no count-bound or parity violation. Supplementary stellar subdivisions separately exercise genuine dual triangles.

## Performance scope

Five randomized paired rounds compare the native complete supplied-cut query, including certificate production and replay, with Regina source conversion, actual cutting, component triangulation and exact recognition. The native route is slower at small multiplicities, by about nineteen times at four copies. It reaches approximate parity at 256 copies and is about 4.82 times faster at 1,024 copies. Raw samples and timing components are retained.

The separate finite benchmark has exactly 2^k spanning trees and a specified enumeration policy that reaches the unique successful tree last. At k=12, enumeration takes a median 283.807 ms, the polynomial solver 0.603 ms, and stopping search 1.109 ms, all including positive replay. This is a controlled comparison with that enumeration policy; it is not a whole-knot speed-up. The smallest finite cases also show overhead, which remains in the tables.

## Archive layout

| Path | Purpose |
|---|---|
| `article/` | Complete article PDF, TeX sections, bibliography and rendered figures |
| `code/make_figures.py` | Regenerate the two benchmark panels from preserved CSV data |
| `code/forest_search/` | Standalone polynomial/general solvers, separate verifier, tests and examples |
| `code/replay_native_packets.py` | Replay the saved source-authenticated positive and negative packets |
| `native/Topology/UnknotRecognition/fast/` | Complete proposed native file versions |
| `integration.patch` | Patch against the pinned commit: two modified files and twelve additions |
| `results/native/` | Corpus/matrix/parity audits, seven positive packets, three negative packets and timing samples |
| `results/forest_search/` | Independent finite audit and controlled benchmark observations |
| `results/package_validation/` | Regression, patch, replay and historical-fixture evidence |
| `results/document_validation/` | Final PDF build and layout verification summary |
| `REPRODUCE.md` | Exact commands and dependency/source requirements |
| `code_manifest.json` | Frozen code and experimental-evidence identities |
| `SHA256SUMS.txt` | Final archive file identities, excluding this checksum file itself |

The native patch enables the geometric BFS reduction and v6 certificate dispatch. The exact forest-choice solvers are separate research tools; they are not silently enabled in the native entry point. The archive contains the proposed files and evidence, rather than a duplicate of the full repository.

## First commands

From the extracted package root:

```bash
python -B check_package.py
```

This checks the frozen code manifest, replays four finite example proofs, regenerates the same certificates, and rejects four mutations. After applying the patch to the pinned repository, also run:

```bash
python -B check_package.py --native-repo /absolute/path/to/ProveIt
```

That additionally authenticates all seven positive native packets and reconstructs and checks all three negative kernels. It does not require Regina. The full corpus comparison and paired native benchmark do require Regina; see REPRODUCE.md.

To regenerate the scientific figure from the recorded measurements:

```bash
python code/make_figures.py
```

This optional command requires Matplotlib. The pre-rendered PDF, SVG and PNG figure files are already supplied.

## Next research priorities

Section 7 gives sixteen explicit questions with hypotheses, scope and success criteria. The immediate priorities are:

1. Resolve the three authenticated annular interface obstructions with a precisely specified geometric extension.
2. Determine the complexity of forest-compatible activation for the native cycle-compatible triple-unit columns.
3. Investigate parameterization by the number and interaction of those columns, and coordinated lower/upper forest choices.
4. Compile transport for arbitrary marked hierarchy patterns through cancellation balls with a proved encoding-growth bound.
5. Bound surface discovery, state visits including resets and failed branches, and cumulative certificate growth against the original diagram size.

The article distinguishes these open obligations from the proved local operators and from Lackenby's announced asymptotic programme. Classical handle cancellation, compressed cutting, stopping sets, Rado's theorem and matroid intersection are attributed to their sources. The new contribution is their specific native geometric and algorithmic connection, with explicit proofs and independently checked implementations.
