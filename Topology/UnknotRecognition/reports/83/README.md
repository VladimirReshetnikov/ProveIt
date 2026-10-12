# Four-copy kernels for compressed boundary patterns

Research continuation for `ProveIt/Topology/UnknotRecognition`, 12 October 2026.

## Main result

For a connected finite **unit-edge graph tile** T with disjoint, injective,
nonempty input/output interfaces of equal width, the complete marked cut
signature at threshold three satisfies

    S_3(T^N) = S_3(T^min(N,4)).

The signature prescribes both boundary colorings and the exact set of colors
having a monochromatic edge; costs above three are saturated at four. The
constant four is optimal, even for the terminal essentiality predicate on
closed cubic planar patterns. It does not depend on the interface width.

Consequently, a **flat** graph descriptor with explicitly stored connected
repeated tiles and binary exponents has a linear-size finite query kernel.
A bounded-flow certificate engine gives polynomial encoded-time answers.
Negative witnesses lift to succinct original-graph colorings and at most
three original edge addresses without expanding large multiplicities.

Read `article/four_copy_patterns.pdf` for the definitions, complete proofs,
sharpness examples, disconnected obstruction, periodic extension, complexity
accounting, and eight further research directions. The article distinguishes
proved results, implemented results, and unproved integration obligations.
The targeted literature review does not establish a priority claim.

## Scope: graph query, not a whole recognizer

The production API handles **closed serial chains of equal-width tiles**.
The contextual theorem covers more general flat wiring than the delivered
assembler. Do not use the implementation as an arbitrary-context importer.

For a faithfully embedded cubic pattern on the boundary of a **separately
certified ball**, the absence of a marked cut of size at most three is exactly
pattern essentiality. The package itself establishes neither that embedding
nor the ball certificate, and never returns an unknot verdict. A query kernel
is not a replacement 3-manifold or a topological simplification.

The native geometry-to-tile adapter, native regression suite, and native knot
benchmarks were **not run**. No remote repository file was modified. An
unrestricted quasi-polynomial unknot recognizer is not established here.

## Run

Python 3.10+ and its standard library suffice for the production package and
unit tests. From this directory on a POSIX shell:

```sh
PYTHONPATH=code python -m unittest discover -s tests -v
PYTHONPATH=code python verify_artifacts.py
PYTHONPATH=code python -m pattern_kernel examples/huge_prism.json --output proof.json
PYTHONPATH=code python experiments/audit.py
PYTHONPATH=code python experiments/benchmark.py
cd article && sh build.sh
```

For PowerShell, first set `$env:PYTHONPATH="code"`, then run the same Python
commands without their `PYTHONPATH=code` prefix. The article needs pdfLaTeX;
`build.sh` invokes it three times. The optional planar-dual audit uses NetworkX
(the retained run used 3.6.1); install `requirements-audit.txt` to reproduce
that part. The rest of the audit does not require it.

The CLI writes a JSON certificate and independently checks it before reporting
`LOW_CYCLIC_CUT` or `NO_LOW_CYCLIC_CUT`. It explicitly reports that no knot
recognition was performed. Source counts are hexadecimal strings so that
very large integers do not depend on decimal conversion limits.

The explicit assembler has a default 100,000-copy cap, also through `solve`;
the signature oracle has an eighteen-local-vertex cap. They are finite
reference tools, not alternative large-input paths. Production reduction
refuses to cap a disconnected tile. Resource exhaustion must never be
interpreted by an integrating caller as a positive topological verdict.

## Retained evidence

All 35 standalone tests pass. The separate seeded audit completed 6,000 full
signature comparisons on 1,500 connected tiles, 180 cubic multigraph checks
against exhaustive colorings, and 25 planar-dual checks. These are exhaustive
checks of sampled finite instances, not an exhaustive classification of all
graphs. Producer-disabled replay and malformed proof cases are tested.

`examples/huge_prism.json` represents 2^16384+1 prism repeats. Its kernel has
eight vertices and twelve edges. The negative example has 2^4096+7 repeats,
one triangle-expansion tile, then 2^1024+9 repeats; its kernel has twenty
vertices and thirty edges and its witness identifies three original cut
edges. Both complete source-bound proofs are included.

The paired benchmark includes finite assembly, graph proof production and
independent proof replay. It excludes source geometry preparation, input
parsing and proof serialization. Five shuffled paired rounds followed a
warmup. At 32 repeats, explicit/kernel median times were 545.921/1.551 ms;
the median paired ratio was 351.250. At one repeat, the ratio was 0.407:
compression and certificate overhead made the tiny case slower. The A/A
control ratio was 0.974. These are **terminal subsystem measurements**, not
whole-recognizer speedups. Raw rounds, small-input regressions and an excluded
incomplete larger benchmark attempt are retained in `experiments/`.

## Integration and provenance

`integration/INTEGRATION.md` defines the geometric adapter and failure
contract. `integration/README-roadmap.patch` is an optional, unapplied
roadmap clarification for the inspected source checkpoint, not an algorithm
patch. `source_manifest.json` pins the reviewed repository files and records
the limited inspection scope. `SHA256SUMS` authenticates the distributed
artifacts; `verify_artifacts.py` checks those hashes and replays both examples.

A suitable initial destination is a new descriptive research folder below
`Topology/UnknotRecognition/reports/`, for example `four_copy_patterns/`.
This package does not select or overwrite a numbered report slot.

The new files are offered under MIT-0, matching the repository's stated
licensing convention. No third-party papers, slides or fonts are bundled.
