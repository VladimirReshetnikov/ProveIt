# Sparse small-cut responses for compressed unknot hierarchies

Research continuation for the ProveIt project, 12 October 2026.

The article and software establish an exact marked-cut evaluator for **supplied edge-owned graph grammars**. For connected pieces and fixed cut threshold, response tables and budget-feasible joins have polynomial size even with large interfaces and arbitrary nested reuse. The threshold-three graph predicate applies to a faithful cubic boundary pattern on a separately certified ball.

**This package does not accept knot diagrams, does not return an unknot verdict, and does not establish an unrestricted quasi-polynomial recognizer.** No upstream files or repository commits were changed.

## Read the article

`article/Sparse_Cut_Grammars.pdf` is the complete article; its source is `article/Sparse_Cut_Grammars.tex`, with generated tables in `article/measurements.tex`.

The main statements are the connected and terminal-component sparse-support theorems, exact gluing, the budget-pair theorem, polynomial connected-grammar evaluation, the component-parameterized quasi-polynomial regime, and succinct witness/address extraction. Existing terminal-cut sparsification and the incoming four-copy work are explicitly credited. Novelty priority is not claimed beyond the inspected repository context.

## Run

Python 3.10 or later and the standard library are sufficient. Recorded runs used CPython 3.13.5 on Linux x86-64.

```sh
PYTHONPATH=src python -m unittest discover -s tests -v
PYTHONPATH=src python experiments/audit.py
PYTHONPATH=src python experiments/benchmark.py
PYTHONPATH=src python src/query.py examples/triangular_prism.json --check
PYTHONPATH=src python src/query.py examples/ladder_2pow256.json --check
```

On Windows, set `PYTHONPATH` to `src` using the shell's environment-variable syntax before running the Python commands.

```sh
cd article
sh build.sh
```

PDF rebuilding additionally requires LaTeX and the packages listed in the source. No font files are distributed.

## Results supplied

37 unit tests pass. The separate audit checks all 772 connected simple graphs through five vertices at thresholds zero through three, 95,768 terminal-subset projections, 1,000 randomized weighted leaves, 1,500 randomized grammars, 4,276 candidate-pair bounds, and 3,277 independently replayed complete certificates. Ten joined-star cases attain the proved degree-k formula. Raw counts and seeds are in `data/audit.json`; unit output is in `data/unit_tests.txt`.

Saved large examples include a connected ladder with 2^257 vertices in 258 rules, a nested nonuniform grammar of depth 128, and 2^128 hidden components. Large numeric graph counts are serialized in hexadecimal. Every saved complete certificate has been replayed against its source grammar. Present marked cuts also have soundness-only witness DAGs and original grammar-edge occurrence addresses.

`data/benchmark.json` retains alternating paired repeats, separate complete-replay timings, A/A controls, and source hashes. `data/benchmark.csv` is a compact table. These are local complete-kernel experiments, not native recognition measurements. The literal comparator is deliberately simple, not a claim about the fastest explicit planar cut algorithm. Small cases can favor literal expansion.

## Files and trust boundaries

- `src/sparse_cuts.py`: producer, sparse tables, metadata, powers, witnesses, and addresses.
- `src/checker.py`: independent leaf-deletion completeness and literal-map replay; imports no producer code.
- `src/reference.py`: capped literal expansion and exhaustive vertex-coloring oracle; also the explicit tree-cut benchmark comparator.
- `src/query.py`: graph-only command line interface, with inconclusive status on explicit producer-budget exhaustion.
- `integration/`: input contract, JSON Schema, native integration checklist, and suggested additive layout.
- `SOURCE_AUDIT.json`, `CLAIMS.md`, `RESEARCH_QUESTIONS.md`: scope, proof status, and next research targets.

A complete response certificate is needed to certify absence of a marked cut. A selected witness proves only existence. The graph metadata checks connected components and cubic degrees, not spherical embedding or ball ownership. The source-faithful geometry adapter and embedded-disc transport are not provided. The native Python/Rust recognizer suites were not executed here.

## Encoding and resource contracts

Edges have strictly positive integral capacities; loops and parallel edges are allowed. All joins use fresh child occurrences, identify only declared terminals, and never identify or delete edges. A forgotten private vertex cannot later become an attachment point without a new authenticated producer operation.

Leaves must explicitly name every vertex in an edge, terminal list, or `isolated_vertices` inventory; one implicit isolated singleton is allowed. This prevents a binary count from hiding an expanded leaf. Use grammar reuse for large multiplicities. Input and table objects are Python data; the CLI's ordinary JSON integer parsing inherits the interpreter's resource limits. The mathematical bit-complexity theorem does not assume unit-cost arbitrary-length integers.

Producer operation and state caps are exploratory controls, not hard memory/wall-time isolation for hostile inputs. The independent checker favors clarity and does not implement the producer's sharp budget indexing. Its cost is therefore reported separately.

## License

New article text and software are released under MIT-0. Referenced prior papers and repository materials are not redistributed by this package and retain their own terms.
