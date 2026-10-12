# Cographic Persistence and Causal Reset Complexity

Research continuation for `Topology/UnknotRecognition`, prepared 12 October 2026.

The article develops a persistence approach to the hierarchy-reset bottleneck. It contains complete proofs of the graph/topology and fixed-dependency results, an explicitly conditional quasi-polynomial accounting theorem, and fifteen concrete further research questions.

## Main results

For connected, pairwise disjoint, cooriented candidate surfaces, the valid simultaneously nonseparating batches are exactly the edge sets whose deletion leaves the chamber graph connected. The integral intersection image is the graph cycle lattice. A single scalar weighted-orbit census recovers the oriented labeled chamber graph, conditional on authenticated source markers and the correct chamber relation. Maximum additive retention reward is obtained by deleting the complement of a minimum-weight spanning tree.

A dual loop crossing a surface once supplies a local nonseparation certificate. Its full source support, not only the surface cells, must survive an edit. A finite source-arena forest provides shared graph-level loop descriptions; compressed native geometric route export remains a separate obligation.

For a fixed acyclic dependency graph with rebuild caps `g[i]` and initial remaining potentials `d[i]`, all version changes satisfy

```
B[i] = d[i] + (g[i] + 1) * sum(B[j] for j in parents[i]).
```

An explicit online potential decreases at every charged event, including rebuilds. Changes to the dependency arena must pay for increases in that potential. Reverse amplification weights turn retained initial progress into additive reductions of the certified bound. The combined optimizer minimizes that bound over valid geometric batches using a minimum spanning tree. The included three-task example lowers the bound from 11 to 4 by retaining earlier progress; retaining only the last task lowers it to 10.

## Scope

These are proved mathematical results and tested finite reference primitives, not a complete new unknot recognizer. A knot exterior has first Betti number one, so its initial nonseparating batch has size at most one. A general quasi-polynomial result still needs sound source-local persistence, controlled intermediate encodings, numerical potential bounds, bounded task creation, and low actual causal depth. The source adapters and native full-recognition benchmark are not implemented or run here.

The graph/MST/cographic foundations and weighted-orbit algorithm are classical. The proposed contribution is the combined certificate, reset accounting, and amplified reuse framework. No exhaustive worldwide novelty or priority claim is made.

## Files

- `article/cographic_persistence.tex` and `.pdf`: article and compiled PDF. The modular source imports the recorded benchmark table from `results/`. `article/cographic_persistence_standalone.tex` is a self-contained copy with that delivered table inlined; regenerate it after changing benchmark data.
- `code/cographic.py`: graph and side-census decoder, optimal batch, finite routing forest.
- `code/causal.py`: forward bounds, reverse amplification, eventwise potential, legal-event scheduler, support intervals.
- `code/reuse.py`: composite causal-retention optimizer.
- `code/verify.py`: independent batch, routing, trace, and composite reuse verifiers; no imports from the producers.
- `code/demo.py`: replayable examples, including the 11-to-4 bound reduction.
- `code/benchmark.py`: paired local comparison with an exhaustive reference and identical controls.
- `tests/test_research.py`: standard-library exhaustive, randomized, mutation, and binary-stress tests.
- `examples/`: generated finite certificates and histories.
- `results/`: actual validation counts, logs, raw paired samples, and generated table.
- `INTEGRATION.md`: proposed native interface and trust boundaries.
- `SOURCE_AUDIT.md`: exact scope of the repository and prior-manuscript inspection.

## Reproduction

From this directory:

```sh
python tests/test_research.py
python code/demo.py
python code/benchmark.py
sh build.sh
```

Python modules use only the standard library. They were tested with CPython 3.13.5. LaTeX compilation needs the packages listed in the article preamble. Run verification on a working copy when preserving delivered evidence: tests and benchmarks deliberately regenerate their own records. Timing values vary by environment.

All 17 test methods passed with no failures or skips. Coverage includes 772 connected simple graphs, 55,895 subset/rank checks, 4,361 side partitions, 320 weighted multigraphs against exhaustive search, 450 finite source arenas, 1,500 path-sum DAGs, 180 exhaustive composite-reuse comparisons, and 16,385-bit integers. These are finite mathematical-model checks, not native geometry tests.

## Placement

Suggested intake: the next available `Topology/UnknotRecognition/reports/<NN>/`, stripping this one wrapper directory. No report number is reserved. This package does not modify `fast/`, change recognition dispatch, or require automatic patch application. Later native integration should be a separately reviewed change.
