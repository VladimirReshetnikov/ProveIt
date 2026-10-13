# Exact Euler mask-tree research

Run the correctness audit from `fast/` with Regina installed:

```sh
python -B -m euler_tree_research.audit --output /tmp/euler-tree-audit.json
```

The audit covers every one of the 64 quadrilateral masks on a fixed two
tetrahedron layered solid torus. Each tetrahedron independently permits any
subset of its three types, including the empty set. It also checks twelve
selected masks each on an interior-vertex solid torus and a solid torus with
multiple boundary vertices. These additional families are controls, not
exhaustive mask enumerations.

For each original source, Regina freshly enumerates all original **standard**
vertex normal surfaces. The oracle target filters these independent vectors
by positive Euler characteristic, non-vertex-link status and containment of
their quadrilateral support in the supplied mask. It uses no native cycle
matrix, anchor choices, eliminated Q coordinates or producer search results.
The complete standard vertex list and source face pairing are retained.

Every supplied mask is solved without caps by both the fixed source model and
the independently rebuilt restricted model, each with both envelope and anchor
strategies. All four answers must agree with the original standard oracle.
Every negative tree passes the independent tree checker. Every positive point
passes original standard matching, compatibility and canonicality checks using
Regina's source identifications. Support extraction must preserve all input
zeroes, and its primitive ray must occur in the fresh standard vertex list.
Regina's exact original-source support rank and labelled crushing quotient are
then compared with the native result, including every component and successor.

The default run also constructs fresh native circle, trefoil and figure-eight
diagram queries with vertex reduction and the fixed source tree. The shared
allowances are 256 nodes, 10,000 pivots and 10,000 anchors. Conclusive results
must pass the independent diagram-bound recognition verifier; an inconclusive
result retains and verifies only its authenticated partial crushing chain.
Every completed crush in either case is compared with Regina's exact labelled
quotient and original-source support rank. A remaining source is recorded as
such: finite allowances never turn an unfinished search into a negative proof.
Use `--supplied-only` to omit these diagram probes.

The JSON retains every complete result, coordinate vector, extraction record,
negative certificate, diagram chain, oracle source and quotient comparison.
`source_hashes()` from `benchmark.py` pins the maintained native package and
research dependencies at both ends of the run. A source change invalidates the
audit. `passed` means that all requested comparisons and replays passed; it does
not mean every bounded diagram query was conclusive.

This audit makes no timing claim. Small certificates or finite fixture success
do not bound general tree size or Bland simplex pivot counts and do not prove
quasi-polynomial unknot recognition.

Run the timing controls and bounded profiles separately, with no competing
CPU jobs:

```sh
python -B -m euler_tree_research.benchmark --output /tmp/euler-tree-benchmark.json
python -B -m euler_tree_research.probe --output /tmp/euler-tree-probe.json
python -B -m euler_tree_research.check_evidence
```

The complete positive controls use nine randomized five-arm pairs, batches of
three queries and three A/A pairs. Both controls terminate during polynomial
vertex preprocessing, so they measure integration overhead, not tree-search
speed. The historical flat-sector driver is pinned to commit `6c2fd5aae`; its
shared dependencies are the current pinned files. This is a driver ablation,
not a whole historical checkout.

The trefoil and figure-eight profiles compare four single runs: historical
preprocessed Q and LP sectors, restricted-model trees, and fixed-source trees.
The flat-sector limit is 64; all LP arms allow 10,000 pivots and 10,000 anchors,
and tree arms allow 256 nodes. These different work units are recorded as
configured bounds, not equated. A 30-second cooperative ceiling also applies.
Construction, search, internal replay and JSON serialization are timed; the
separate independent replay is outside the timer. An explicit cancellation
returns no partial proof, while an ordinary `INCONCLUSIVE` retains an
authenticated chain. Only conclusive outcomes are full recognition timings.

The saved-evidence checker reads `synthesis/data/euler-tree-{audit,benchmark,probe}.json`,
replays certificates without discovery, checks source pins and timing
arithmetic, and writes the article table. `--publication` additionally records
a manifest of evidence, tests, article sources and the compiled PDF.
