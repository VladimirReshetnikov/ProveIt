# Conflict-transversal research evidence

This package audits the optional native `search_euler_transversal` policy and
its diagram-bound `sector_method='transversal'` integration. It does not claim
a general quasi-polynomial running time or a universal small transversal.
The proof and explicit remaining hypotheses are in
`../../synthesis/euler_transversal.tex`.

Run from `Topology/UnknotRecognition/fast`:

```sh
python -B -m euler_transversal_research.audit --output ../synthesis/data/euler-transversal-audit.json
python -B -S -m euler_transversal_research.check_evidence
python -B -m euler_transversal_research.benchmark --output ../synthesis/data/euler-transversal-benchmark.json --pairs 5 --aa 1 --batch 1
python -B -S -m euler_transversal_research.check_evidence --benchmark ../synthesis/data/euler-transversal-benchmark.json
```

Run the timing command with the CPU reserved for that experiment. After the
article and PDF are rebuilt, add `--publication` to the last command to write
the publication manifest. The audit and benchmark pin the entire native Python
package, all research dependencies inherited from the Euler-tree audit, and
all Python, JSON fixtures, and Markdown in this package. Pins are checked at
both ends of a run. Store generated evidence outside this package.

## Correctness scope

The correctness audit enumerates fresh Regina **original STANDARD** vertex
surfaces on three supplied sources. It tests all 64 masks on a two-tetrahedron
layered torus and 12 masks each on sources with an interior vertex and multiple
boundary vertices: 88 masks, each under both envelope-first and anchor-only
search. Incompatible root masks are deliberate. Positive answers must agree
with an allowed positive nonlink original standard vertex; canonical positive
coordinates undergo native full-source extreme-ray extraction, fresh original
matching checks, and native/Regina labelled crushing-quotient comparison.
Negative answers replay the existing independent complete branch-tree proof.

Fresh diagram runs use the crossing-free circle, the braid `(2; 1,1,1)`, and
`(3; 1,-2,1,-2)`. Each full recognition proof and every crushing quotient is
replayed. The finite transversal lower bounds additionally use retained root
ray discoveries in `data/lower_witnesses.json`. These are **not** fresh or
exhaustive root-ray enumeration. Every retained ray is freshly checked for
original standard matching, nonnegative integral coordinates, canonical
triangle minima, positive formal Euler, Q matching, primitive Q coordinates,
and support nullity one in the independently derived Q equations. Incompatible
coordinates are formal vectors, not embedded surfaces. Disjoint complete
conflict sets prove a lower bound; the final complete negative tree proves an
upper bound using the union of its split tetrahedra. Exact labelled endpoint
equality is mandatory, so these numbers cannot be transferred merely by knot
type or tetrahedron count.

The solver-free checker runs without Regina (`python -S`), discovery, LP
optimization, or new timings. It verifies listed original standard rays and
all saved comparisons; completeness of the saved original-standard lists
remains evidence from the audit's fresh Regina enumeration. It independently
replays all native negative and crushing proofs and reconstructs both finite
transversal bounds.

## Timing scope

The paired benchmark compares the ordinary source-model DFS with optional
transversal learning, including all native exterior construction, shelling,
vertex preprocessing, failed candidates, subset filtering, LP work, internal
replay, and result serialization. Imports, prepared diagram objects and a
separate independent warmup replay are excluded. Five paired samples use a
fixed shuffled order; one shuffled tree/tree A/A pair is retained per case.
The checker replays every warmup, checks exact timed output digests, verifies
the shuffle sequence and elapsed-time arithmetic, and recomputes medians and
paired ratios.

Both arms use the same finite shared allowances. The expected figure-eight
DFS outcome is `INCONCLUSIVE`, whereas learning completes `KNOTTED`.
Its elapsed-time ratio therefore compares different outcomes and must not be
reported as a speedup between two completed recognitions. Circle and trefoil
have equal conclusive outcomes. The policy remains optional: minimum-subset
learning can be worse than ordinary DFS, and a universally small resolving
set has not been proved.
