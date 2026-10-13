# Complete raw versus visible-factor crushing workloads

This is evidence for the additive `recognize_factored_by_crushing` API. It does
not alter or benchmark the existing high-level `recognize` router, which already
factors visible connected sums. It makes no claim that a supplied diagram's
visible factors are the knot's hidden prime factors, or that a bound on child
parameters bounds the conflict parameter of a triangulated connected sum.

## Predeclared audit

Eight actual diagrams are used: circle; trefoil braid `(2;1,1,1)`; figure eight
`(3;1,-2,1,-2)`; UU `(3;1,2)`; UT `(3;1,2,2,2)`; TT `(3;1,1,1,2,2,2)`;
TF `(4;1,1,1,2,-3,2,-3)`; FF `(5;1,-2,1,-2,3,-4,3,-4)`.
Each whole diagram is passed to the raw driver and the factorwise driver.
This is 16 returned-workload records, not eight hand-picked child searches.

Both arms receive exactly the same explicit options: transversal search with
the conflicts candidate policy, source model, envelope strategy, polynomial LP,
vertex reduction and optional inverse boundary layering. The whole-call limits
are 256 tree nodes and 10,000 pivots, anchors, candidate states, ellipsoid
iterations and feasibility calls; unused corner controls remain 256 sectors and
10,000 bases. The mixed reduction allowance is unbounded. In the factored arm,
these limits are shared across every attempted child. No wall cutoff is imposed.

Every returned `INCONCLUSIVE` result is retained with all partial work and
independently checked child/source chains. A stopped or exceptional whole call
leaves `passed=false`, incomplete coverage and an explicit `unreturned_calls`
entry; it is never converted to a completed negative result. The artifact is
saved after each returned arm. Formal source-pinned runs must finish all declared
calls; an interrupted file is useful diagnostic evidence only.

The optional `--scaling` audit adds four wrapper-only inputs: visible sums of
2, 4, 8 and 16 same-sign trefoils, presented by `(k+1;1,1,1,2,2,2,...,k,k,k)`.
All configured work and the first necessary negative factor proof are retained.
These four calls have separate declared coverage and are not part of the raw
versus factored eight-case comparison or the timing protocol. Their status and
number of attempted factors are observed, not assumed.

## Independent replay

`check_evidence.py` imports no discovery routine. It independently reconstructs
factor PDs from the original traversal and supplied interlacement components,
checks the forest and separation conditions, verifies every returned conclusive
child certificate or partial chain, and enforces the outer quorum. It checks the
deterministic attempted-factor prefix, each charged counter's integer type and
limit, recomputed sum/peak totals, and all nine shared limits. It does not rerun
LP discovery to reconstruct an operation trace. Initial and shelled tetrahedron counts are totals
over attempted factors. They are not a size for a single combined exterior.

Full source pins include every native Python file and every immutable file in
this research package. Research outputs live outside the package and are not
included recursively in their own pins. No historical artifact is relabelled as
a fresh experiment. Neither Regina nor a polynomial knot invariant supplies the
correctness claim; it comes from the independent exact native certificates.

## Predeclared 50-call paired protocol

Five cases are fixed in advance: circle, trefoil, figure eight, UU and UT. For
each, run one warmup per arm, three alternating raw/factored pairs, then one raw
A/A pair: 10 calls per case, 50 total. Pair order is raw/factored when
`(case_index+round_index)%2==0`, reversed otherwise. No result-dependent case
selection or wall cutoff is used.

Imports and validated input PD preparation occur before timing. Every timed
call includes fresh complete recognition, independent certificate/partial replay,
canonical JSON serialization of the complete returned result, and SHA256 hashing.
The runner preloads the selected native backend and rejects a call that initializes
another native module inside its timer. Complete warmup outputs are retained;
paired and A/A samples retain nanoseconds, status, serialized bytes and result
hash. Every sample must match the full audited result for that exact arm.

Only cases where both arms return the same conclusive whole-diagram verdict
are eligible for a recognition speed ratio. Inconclusive records retain times
and counters, but their raw/factored ratio is explicitly absent. Report the
median of paired ratios, each arm's median, and the raw A/A ratio. No asymptotic
speed theorem follows from these finite timings.

Run from `Topology/UnknotRecognition/fast` after all sources are frozen:

```sh
PYTHONPATH=. python -m factored_crushing_research.audit --output ../synthesis/data/factored-crushing-audit.json
PYTHONPATH=. python -m factored_crushing_research.check_evidence --audit ../synthesis/data/factored-crushing-audit.json --output ../synthesis/data/factored-crushing-audit-check.json
PYTHONPATH=. python -m factored_crushing_research.benchmark --audit ../synthesis/data/factored-crushing-audit.json --output ../synthesis/data/factored-crushing-benchmark.json
PYTHONPATH=. python -m factored_crushing_research.check_evidence --audit ../synthesis/data/factored-crushing-audit.json --benchmark ../synthesis/data/factored-crushing-benchmark.json --output ../synthesis/data/factored-crushing-replay.json
```

Use `--scaling` on the audit command to include the optional repeated-trefoil
controls. Output JSON uses compact separators; full proofs remain present.
Python `-O` is unsupported because this research package uses assertions.
