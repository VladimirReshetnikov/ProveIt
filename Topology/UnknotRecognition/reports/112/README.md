# Lazy Weight Replay and Native Chamber Graphs for Unknot Recognition

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

**Source pin:** e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39.

The article contains complete proofs of two local contributions, their native implementations and independent checks, all measured results, and fourteen proposed research directions. It does **not** establish a general quasipolynomial unknot recognizer.

## Start here

- **article/Lazy_Replay_and_Native_Chamber_Graphs.pdf** — the comprehensive article.
- **article/Lazy_Replay_and_Native_Chamber_Graphs.tex** — the main LaTeX source; all included sections, bibliography, tables and figures are present.
- **integration/README.md** — the six-file source patch, overlay, standalone runtime, source provenance and application instructions.
- **results/** — retained original observations and logs, including unfavorable timing results and inherited baseline-test failures.
- **examples/** — two complete native source/certificate packets.
- **reproduce.py** — the default standalone check and optional experiment entry point.

## Contributions and precise scope

### Lazy vector additions in independent certificate replay

The former verifier rebuilds flat run partitions and repeatedly visits complicated receiving intervals. The new deterministic AVL sequence stores integer lengths and delays uniform vector additions at subtree roots. Adding the same vector preserves every internal run inequality, so only split/join seams require canonicalization.

For R current runs and S removed suffix runs, a translation fold needs

O((S+1) log(R+2) + S log(S+1))

structural/endpoint operations and O(d(S+1) log(R+2)) coordinate operations for d-dimensional weights. Reflection has no residue-sort term. The fine bound separately charges binary arithmetic, source preparation, histogram dictionaries, and unchanged unweighted trace work.

A complete legal native AHT star family has H one-run suffix folds into a prefix with L alternating runs. The old weight work is Omega(HL); the lazy tree work is O(L + H log(L+2)). This is a proved separation for the specified replay methods, with explicit whole-verifier map-cost qualifications. It is not asserted to be a family of geometrically realized hard knots.

The existing sharp run-growth bound R <= R0 + 2T and classical AHT polynomial weighted counting are attributed to their earlier sources. The producer and separate least-representative checker retain their independent original paths.

### Native chamber-graph authentication

The new observer takes one admissible normal surface and a proposed normal-disc representative for every component. A scalar orbit census authenticates that the labels are exhaustive and distinct. The normal double authenticates two-sidedness. A second scalar census places the two sides of every component in the actual cut chambers.

An independent verifier reconstructs side locations through raw cut-cell charts. The resulting graph G determines every labelled subcut:

number of connected components after cutting labels J = number of components of G with edges J deleted.

It therefore supplies actual geometric input to report 92's cographic batch criterion. For nonnegative additive rewards, a maximum-reward nonseparating batch is the complement of a minimum spanning tree. The graph does not prove incompressibility, a handlebody conclusion, or persistence through a later edit.

The explicit component count k is an input/output parameter. Huge parallel multiplicity cannot be expanded into a k-edge output at a cost polynomial in log(k) alone. Current dense scalar masks can use O(k^2) bits.

## Evidence

| Experiment | Recorded result |
| --- | --- |
| Focused native replay regression | 52 passing tests, including the maintained 157-source moment bank |
| New standalone tests | All 18 methods passed using the bundled snapshot |
| Native chamber corpus | 80 accepted graphs, 19 correctly refused one-sided systems, 7 incomplete-label refusals |
| Exhaustive labelled subcuts | 254 comparisons, each against two independent literal constructions |
| Complete synthetic weighted verification | Median baseline/new ratios 4.073, 10.404, 19.456 and 38.972 |
| Native whole-cut replay, sum of case medians | 6.122913 s to 5.198893 s, ratio 1.1777 |
| Complete native query, sum of case medians | 14.109865 s to 14.364058 s, a measured 1.8% regression |
| Large connected-meridian packet | 128 tetrahedra, 2,791,715,456,571,051,233,611,642,548 normal discs, 89-bit maximum coordinate, one graph loop |
| Full maintained regression audit | All 1,741 declared methods exercised across the broad run and restored-fixture rerun; two failures reproduced on the pristine baseline |

The complete-query regression is retained. A timing discrepancy in the unchanged producer on the largest native case dominated that aggregate; its cause was not established. The large connected-meridian measurement exercises the maintained single-orbit shortcut, so it is a graph-feasibility example, not an extra lazy-fold speed benchmark.

Two older maintained tests contain refusal expectations that conflict with the pinned adaptive lower-forest tests. Isolated exact-pin and patched runs reproduce the same two assertion failures: actual COMPLETE versus expected INCONCLUSIVE. The affected tests remain unchanged. Full tracebacks and source authentication are in results/baseline_failure_audit.json and its log.

An initial verbose full-suite attempt was interrupted during a temporary filesystem-capacity incident; its partial log is retained as full_native_suite_interrupted.log. The completed compact-output run executed 1,733 tests in 499.532 seconds. One class could not start because an external fixture had been omitted from the local sparse checkout; after restoring the exact pinned fixture, all eight affected tests passed. The two logs together cover all 1,741 declared methods. The only remaining failures are the two inherited assertions documented above.

## Reproduce the bundled checks

Python 3.10+ is required; the recorded interpreter is Python 3.12.14. The default checks use only Python's standard library and the supplied native source:

```sh
python reproduce.py
```

This checks all integration payload hashes, executes the eighteen new test methods, and independently verifies both stored geometric packets. No Git checkout, network connection, Regina, or external topology service is required for this command.

Optional experiments:

```sh
python reproduce.py --synthetic
python reproduce.py --native
python reproduce.py --chamber-audit
```

These write fresh observations under reproduced/ and leave the original results/ unchanged. The original benchmark uses three paired rounds, includes the source checks identified in the article, and preserves exact result digests.

The full unrelated maintained suite and the exact-pin inherited-failure audit require a ProveIt checkout with their original test dependencies. The compact snapshot is sufficient for the commands above; it does not contain the whole historical repository.

## Rebuild the article

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  Lazy_Replay_and_Native_Chamber_Graphs.tex
```

All static figure assets are included. To recreate the figure and tables from retained JSON, install Matplotlib and run this from the archive root:

```sh
python scripts/make_figures.py
```

## Integrate the patch

The patch changes only the ordinary weighted verifier and adds the run rope, chamber observer/checker, and their two test modules. It was applied in a clean temporary repository containing the exact pinned source, and all resulting files were compared byte for byte with the overlay.

```sh
git apply --check /path/to/archive/integration/proveit_lazy_replay_chamber_graphs.patch
git apply /path/to/archive/integration/proveit_lazy_replay_chamber_graphs.patch
```

Run those commands in a review checkout at the source pin. Later overlapping changes require source review and a fresh regression run. No remote commit, pull request, or publication was made as part of this research delivery.

## Research priorities

The article develops fourteen concrete questions. The most immediate are lazy least-representative replay, output-sensitive automatic component representatives, and compressed geometric dual routes with independently authenticated source support. The next geometric milestone is carrying such a route and its required predicates through one actual hierarchy edit. Global quasipolynomial accounting still requires bounds on all visited states, source and pattern sizes, search, certificate generation, and genuine invalidations.

## Provenance and license

The immutable source pin, original/current file hashes, exact baseline verifier and integration payload manifest are supplied. MANIFEST.sha256 covers the delivered archive contents except itself. The native source retains the repository's MIT No Attribution license and the existing nested component license. Primary mathematical sources and prior ProveIt contributions are cited in the article; their external PDFs are not redistributed.
