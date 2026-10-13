# Optional fixed-total-U=1 Pachner descent preprocessing

This package compares the same bounded whole-diagram crushing recognizer with
`reduce_pachner_descent=False` (`baseline`) and `True` (`u1`). Both arms enable
vertex reduction, boundary peeling and strict 3→2 preprocessing. The optional
macro searches from zero cochain with total upward budget one, accepts only an
independently checked first strict descent, then restarts preprocessing. Each
accepted macro decreases the tetrahedron count by one and contains at most
three elementary moves. The public default remains off.

These finite controls do not prove general quasi-polynomial recognition,
monotonicity of the resolving-set parameter, or a universal performance gain.
The separate visible-factor wrapper is not exercised: every diagram is passed
to the raw whole-diagram crushing driver, including the two-trefoil sum.

`common.py` fixes the seven inputs and both complete option maps: circle,
trefoil, figure eight, TT=braid(3,[1,1,1,2,2,2]), T25=braid(2,[1]*5),
T27=braid(2,[1]*7), and W34=braid(3,[1,-2]*4). The explicit braid labels define
the experiment. All calls use the transversal conflict policy, polynomial LP
backend, 256 tree nodes, and 10,000 pivots, anchors, candidate hitting subsets,
ellipsoid iterations and feasibility calls. The nine shared budget contracts
include `max_crushes`, which charges one per crushing, boundary peel, strict
3→2 move or accepted U1 macro. This experiment leaves that cap unlimited;
strict tetrahedron descent bounds the number of accepted operations. Macro
search nodes/work are retained separately, including unsuccessful searches.

The fresh audit makes fourteen genuine whole-driver calls, seven inputs under
both arms. It retains every returned result before replay, with complete or
partial certificates, all counters and exact options. An INCONCLUSIVE return is
not a recognition verdict. No wall cutoff or filtering removes difficult calls.
Exceptions leave `passed=False`, the active call, any returned result, and
explicit failure/incomplete coverage. Archival replay is separate coverage.

The benchmark is predeclared on circle, trefoil, figure eight, TT and T25. It
makes one warmup per arm, three alternating-order pairs and one baseline A/A
pair per case: fifty calls altogether. Each timer includes fresh whole
recognition, independent conclusive/partial replay, canonical full-result
serialization and SHA256. Imports and prepared input PDs are outside. Warmups
retain full results; every sample must match its complete audited result.
Ratios require the same conclusive verdict in both arms. A/A controls remain
visible; finite timings support no statistical population claim. T27 and W34
remain part of the fourteen-call audit even though the benchmark excludes them.

Run from `Topology/UnknotRecognition/fast`, after native and research source
freeze:

```sh
PYTHONPATH=. python -m pachner_descent_research.audit \
  --output ../synthesis/data/pachner-descent-audit.json
PYTHONPATH=. python -m pachner_descent_research.check_evidence \
  --audit ../synthesis/data/pachner-descent-audit.json
PYTHONPATH=. python -m pachner_descent_research.benchmark \
  --audit ../synthesis/data/pachner-descent-audit.json \
  --output ../synthesis/data/pachner-descent-benchmark.json
PYTHONPATH=. python -m pachner_descent_research.check_evidence \
  --audit ../synthesis/data/pachner-descent-audit.json \
  --benchmark ../synthesis/data/pachner-descent-benchmark.json
```

Generated outputs belong outside this package. Source pins include all native
Python modules, every file in this package, and the strict32/composition research
packages used for independent archival source/rank replay. Caches are excluded.
Audit and benchmark require the same complete pin map at start and finish. The
independent checker performs no discovery; it replays saved certificates, binds
input PDs and exact configs, validates coverage/counters and recomputes sample
hashes, order and ratios.

## Exact historical archives

`data/manifest.json` identifies two separate immutable artifact groups. Each
preserves the exact files listed in its original manifest, plus that manifest.
Later scratch review memos are deliberately excluded. JSON is deterministically
gzipped; stored and uncompressed lengths and SHA256 values are recorded.
Embedded native pins are historical generation/replay provenance, never claims
that old scripts ran on today's source. Original scripts retain their scratch
paths. Use the current checker for portable solver-free replay.

The `strict-descent-next-design` group has 29 original manifest-listed files.
It retains three diagram-authenticated strict32-only labelled torus/weaving preprocessing
calls, three once-capped source queries, three separately capped supplied-source
zero-height U1 macro searches, and their original scripts/replays. The labelled
15-tetrahedron T25 source has exact h=3: a complete negative tree gives a size3
upper bound, and three disjoint conflicts of independently checked original
STANDARD root rays give the lower bound. The 21-tetrahedron T27 source has h≥3
only; its capped Euler query is INCONCLUSIVE. W34 at34 tetrahedra also remains
INCONCLUSIVE. The separate T8→7, F12→11 and TT17→16 macro packets have one upward
and two downward moves each. This group precedes native macro integration.

The `fixed-u1-staged-audit` group has seven original manifest-listed files.
Its exact twenty-call protocol consists of two genuine circle wholecalls,
twelve preprocessing-only wholecalls with `max_tree_nodes=0`, and six once-only
supplied-source queries on enabled endpoints. It is not a fourteen-call whole
recognition audit, and source-query counters are never added to preprocessing
counters and described as a fresh wholecall. Five complete diagram recognition
proofs are explicitly assembled from retained authenticated partial chains and
separate full-root negative source proofs.

| Diagram | Baseline tets | Enabled tets | Accepted macros | Enabled query | Exact h |
|---|---:|---:|---:|---|---:|
|trefoil|8|7|1|NO_POSITIVE_EULER|1|
|figure eight|12|10|1|NO_POSITIVE_EULER|0|
|TT|17|16|1|NO_POSITIVE_EULER|2|
|T25|15|11|3|NO_POSITIVE_EULER|1|
|T27|21|17|4|NO_POSITIVE_EULER|2|
|W34|34|31|3|INCONCLUSIVE|unknown|

All twelve preprocessing calls use zero LP work. Baseline packets are exact
literal prefixes of enabled packets. The figure-eight macro reaches11 before
an additional strict32 move reaches10. Solver-free replay checks all ten
unique exposed positive rays with original STANDARD matching/rank and incidence
Euler, retaining every triangle column. Complete negative trees give upper
bounds from actual split sets. Disjoint conflicts give lower bounds; h=0 on F10
follows from a negative unrestricted-root leaf, not an empty observed sample.
No extra LP/ray discovery was used for those lower bounds.

The old group contains eleven unique exposed rays; the staged group contains
ten. Handoff prose was corrected before archival freeze, without changing raw
audit or replay outputs.

These comparisons concern exact labelled triangulations. The reduction of h
in these controls does not establish a general monotonicity theorem or a
polylogarithmic bound after fixed-U1 exhaustion. Known knot type alone never
establishes a negative canonical cone. W34 remains an explicit capped partial
outcome, with no nontrivial h conclusion retained here.
