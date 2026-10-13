# Next strict-descent and prime-source experiment

Scratch only; native and published research sources stay unchanged. The initial
design was read-only during the strict-Pachner benchmark. Root released the CPU
after all 30 calls finished and authorized the bounded experiments in probe.py.
This memo states the design and proved code-level observations; individual
retained phase JSON files are the authority for completed finite outcomes.

## Available independently replayed simplifiers

The maintained native triangulation move inventory contains boundary shellings,
normal crushing, inverse boundary layering, and Pachner 2→3/3→2. I found no
native 2→0, 4→4, or edge-collapse constructor paired with an independent
topological verifier. simplify.py instead changes PD diagrams by Reidemeister
moves; it is not a supplied-triangulation replacement certificate.

There is an already implemented stronger strict *macro*: the fixed-upward
first-descent primitive in pachner_cover_search.find_pachner_descent, replayed
by pachner_cover_verify.inspect_pachner_descent. The supplied-source certificate
is pachner-cochain-endpoint-v1. It includes each actual 2→3/3→2 replacement,
exact source/successor arrays, and independently checked integral cochain
transport. The old optional pachner_epochs recognizer uses this primitive for
positive coherent-disc discovery. It is separate from the new crushing driver.

The bound is on the TOTAL number U of upward events in one epoch, not merely
the maximum excess tetrahedron count. A first strict descent has u≤U and
d=u+1, so at most 2U+1 moves. At a source with no legal 3→2 move, U=1 can only
descend through one upward move followed by two downward moves. With U fixed,
even literal bounded-depth branching is polynomial; the maintained connected
cover theorem gives the sharper 2^O(U) poly(t+B) bound. Its sufficient connected
initial cover size is min(t,3U+3). Existing synthesis/pachner_native.tex and
pachner_epochs.tex already explain this theorem, so it is not a new theorem
of the current slice.

All-zero height rows are valid for the existing transport checker: every signed
global edge difference is zero; the five formal bipyramid heights can all be
zero; the transported coherent normal coordinates and Euler jumps remain zero.
Thus zero heights allow the geometric first-descent primitive to run without
a meridian cocycle, normal-disc counting, or a new topology claim. This is an
algebraic inspection of the implementation, corroborated only when a saved
descent certificate actually replays. An exhausted fixed-U search is a bounded
move-family result, never a negative knot verdict or a minimum triangulation
certificate. An interrupted search says even less.

Current diagram-crushing-v3 accepts single strictly shrinking operations, not
upward intermediate steps. Any future integration should introduce a strict
macro packet with a source-bound endpoint proof; verify every intermediate
finite source, U bound and final strict descent. The mixed reduction budget
must explicitly count accepted macros versus elementary moves; diagnostics
should expose both. Keep old v1/v2/v3 meanings unchanged. Reset all Euler
algebra, dual caches and conflict constraints at the final changed source.
Guard callbacks around legacy producer catches before offering the new API.
No such integration is made here.

## Fixed prime-family source sample

The exact braid labels are T(2,5)=closure(2,[1,1,1,1,1]),
T(2,7)=closure(2,[1,1,1,1,1,1,1]), and
W(3,4)=closure(3,[1,-2,1,-2,1,-2,1,-2]). The last is the standard alternating
weaving projection. No external knot identification or primeness test is used
as a negative-cone certificate.

For context, T(2,q), q odd and ≥3, has bridge number two. Schultens supplies
primary proofs of the torus bridge-number formula and bridge-number additivity:
https://www.math.ucdavis.edu/~jcs/pubs/tknots.pdf (opening theorem), and
https://arxiv.org/abs/math/0111032 (abstract/theorem). Since both nontrivial
summands would have bridge number at least two, these imply primeness for the
two torus inputs. The weaving naming convention is defined on page 1 of
Champanerkar–Kofman–Purcell, https://arxiv.org/pdf/1506.04139v2. The present
experiment needs only the exact braid labels. It does not spend a further
computation proving W(3,4) prime; nor does it infer Euler-cone negativity from
a known knot type.

Phase A calls the real diagram driver with max_tree_nodes=0, vertex reduction,
inverse boundary peeling and strict32 enabled. It independently replays the v3
partial chain and checks zero LP calls/nodes. It records the exact labelled
endpoint, verifies one finite vertex and one torus boundary, and repeats both
local scans to establish a genuine UNCHANGED endpoint for these policies.

Phase B makes exactly one full-root supplied-source transversal query per
endpoint. Explicit controls: envelope/conflicts, polynomial LP, 256 oracle
nodes and 10,000 pivots, anchors, tested hitting subsets, ellipsoid iterations,
and feasibility calls. Every returned outcome is retained. NO_POSITIVE_EULER
requires independent full-root tree replay. The union of its split tetrahedra
is a resolving set and hence a source-specific upper bound on h. POSITIVE_EULER
requires direct matching/admissibility/Euler replay; such a source is not a
negative terminal source and must be crushed before any negative-source claim.
INCONCLUSIVE supplies no h upper bound.

A scratch-only observational wrapper copies positive points already exposed by
the oracle; it performs no extra LP or ray enumeration. If lower-bound evidence
is desired, those saved points must separately pass original STANDARD matching,
canonical Euler and support-nullity-one checks. Coordinate-face extremality
then makes their full conflict sets necessary constraints on every resolving
set. An observed hypergraph upper transversal is not a global h upper bound.
No finite sample supplies a general polylogarithmic theorem.

## Separate upward-move controls

The existing exact archived negative endpoints T8, F12 and TT17 are used, with
source arrays drawn from strict_pachner32_research's immutable original query
archive. One zero-height U=1 query per source has max_nodes=256,
max_work=200000, max_regions=10000, max_oracle_states=10000. Returned local
certificates are independently replayed. A miss at these finite controls does
not exclude all one-upward descents unless the status is the actual complete
bounded-descent status. These controls answer a different question from the
new prime-family Euler probes and are retained separately.

## Reproduction and provenance

Each command writes a separate JSON record, initially passed=False, containing
full current native source pins, this script's hash, exact options, source
arrays, complete returned result and replay summary. Exceptions preserve an
explicit unreturned-call record. Each successful phase checks native pins again.

```
python -B /tmp/strict-descent-next-design/probe.py preprocess T25
python -B /tmp/strict-descent-next-design/probe.py preprocess T27
python -B /tmp/strict-descent-next-design/probe.py preprocess W34
python -B /tmp/strict-descent-next-design/probe.py query T25
python -B /tmp/strict-descent-next-design/probe.py query T27
python -B /tmp/strict-descent-next-design/probe.py query W34
python -B /tmp/strict-descent-next-design/probe.py descent T8
python -B /tmp/strict-descent-next-design/probe.py descent F12
python -B /tmp/strict-descent-next-design/probe.py descent TT17
```

No monotonicity of h under Pachner moves is assumed. A local simplifier can
remove or create positive formal root rays and change all supports. The missing
theorem remains a uniform structural bound for simplified source conflict
hypergraphs, or a genuine family of independently verified growing lower bounds
that survives the justified simplifications. Finite ease is evidence for a
next experiment, not evidence of quasi-polynomial asymptotic recognition.
