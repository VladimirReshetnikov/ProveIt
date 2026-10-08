# Faster terminal boundary patterns

This module decides essentiality of a boundary pattern on a **known 3-ball**.
It improves the report-06 terminal checker from an O(E^4) enumeration of
small edge cuts to deterministic O(s log(s+2)) word-RAM operations, where
s = 2E is the number of darts. It includes validation and negative witnesses.

The topology of the ambient manifold is a caller precondition. This module
does not recognize 3-balls, construct a hierarchy, transport a terminal disc
back through one, or recognize an unknot by itself.

## Run

From the package root:

~~~sh
python -m unittest hierarchy.test_ball_patterns -v
python -m hierarchy.benchmark_patterns
python -m hierarchy.ball_patterns hierarchy/examples/triangle_obstruction.json
~~~

Python 3.9 or newer; standard library only. The stored run used Python 3.12.14.

~~~python
from hierarchy.ball_patterns import classify_pattern, verify_violating_witness
from hierarchy.fixtures import bipyramid

raw = bipyramid(3)
result = classify_pattern(raw)
assert result["status"] == "violating"
assert result["witness"]["kind"] == "nonfacial-dual-triangle"
assert verify_violating_witness(raw, result["witness"])
~~~

## Input

~~~json
{
  "ambient": "3-ball",
  "rotation": [[0, 2, 4], [1, 5, 3]],
  "circles": 0
}
~~~

Every vertex supplies a cyclic triple of darts. Dart 2e is paired with
2e+1. The complete dart list must be exactly 0, ..., 2E-1. Loops and
parallel edges in the primal graph are supported. Each graph component must
give a spherical rotation system; positive-genus components are rejected
even when another component already forces an inessential verdict.
The circles field counts vertex-free circle components and may be large in binary.

The empty pattern and one circle are essential. Every disconnected nonempty
pattern is inessential, independently of the relative nesting of its components.
Relative nesting is not encoded, so a disconnected witness certifies existence
of a zero-intersection curve without selecting a geometric representative.

## Algorithm

The connected graph case constructs the embedded dual. It returns a
violating witness for a dual loop, a pair of parallel dual edges, or a
nonfacial dual triangle. If these do not exist, the pattern is essential.
Once the dual is simple, a degree-at-most-five peeling order yields at most
ten candidate neighbor pairs per dual vertex. All searches use sorted arrays
and binary search; the complexity does not depend on probabilistic hashing.

The primal vertices record *face occurrences* in the dual. In the K3
exception, the same three-cycle bounds two distinct faces; the implementation
retains both occurrences and accepts it. There is no special generic
four-connectivity call.

A negative witness lists dual vertices, crossed primal edge labels, and both
primal vertex sets after deletion. The verifier checks the edge bond by
primal connectivity, independently of triangle enumeration. For a triangle
it requires more than one primal vertex on both sides.

## Verification and benchmarks

The tests exhaust all 10,410 dart pairings at two or four cyclically ordered
trivalent vertices. They compare all 5,628 spherical inputs with the unmodified
report-06 classifier and reject the remaining 4,782 positive-genus inputs.
Connected negative witnesses are also checked by the report-06 witness verifier.

Additional tests cover random larger ribbon maps; 55 random triangulated
spheres with stellar subdivisions and edge flips; relabeling, rotation and
mirroring; all witness types; malformed input; witness corruption; exceptional
small maps; disconnected inputs; and a complete 60,000-dart accepted scan.

benchmark_results.json contains every timing repetition and the input
generators. Both measured calls start with the same prepared JSON-like
dictionary and include validation, embedding checks, classification and
result construction. Fixture generation and external JSON parsing/writing
are excluded. The report-06 wrapper invokes its unmodified classifier with
one validation. These are terminal-subroutine measurements.

## Files

- ball_patterns.py: production classifier and independent negative verifier.
- fixtures.py: deterministic and random spherical-map generators.
- test_ball_patterns.py, test_results.txt: differential and adversarial tests.
- benchmark_patterns.py, benchmark_results.json: reproducible full-call comparison.
- baseline_report06/: exact fetched comparison sources and Git blob provenance.
- terminal_patterns.tex: self-contained criterion, algorithm, proof and scope.
- weight_expansion_obstruction.tex: a precise output-size obstruction for
  normal-coordinate cutting, with the connectedness/two-sidedness caveat.

## Sources

The topological setting is Marc Lackenby, *Incompressible surfaces, hierarchies
and unknot recognition*, arXiv:2607.23350v1, especially Proposition 2.6 (p. 6),
Proposition 9.1 (p. 35), Proposition 10.2 (p. 37), Proposition 14.2 (p. 50),
and Theorem 14.4 (p. 51):
https://arxiv.org/abs/2607.23350

The comparison source is ProveIt's report-06 patterns.py:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Topology/UnknotRecognition/reports/06/unknot/patterns.py

The new complexity bound is for the delivered terminal classifier. It does
not turn the July 2026 hierarchy algorithm into a quasipolynomial recognizer.
