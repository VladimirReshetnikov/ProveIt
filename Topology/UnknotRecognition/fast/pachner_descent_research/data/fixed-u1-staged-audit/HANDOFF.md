# Completed fixed-total-U=1 staged audit

Exactly twenty authorized calls completed with unchanged native source pins:
two genuine whole-driver circle calls, twelve preprocessing-only whole-driver
calls on six noncircle diagrams with the policy off/on, and six once-only
supplied-source Euler queries on the enabled endpoints. `audit.json` retains
all returned results, exact configs, diagrams, source arrays, proofs, partial
chains, counters and every exposed positive point. There are no unreturned
calls or recorded failures. The two whole circle calls return UNKNOT.

This protocol does not measure running time. In particular the source query
counters must not be added to preprocessing counters and labelled as a fresh
whole-driver run. Five complete KNOTTED proofs were assembled from authenticated
preprocessing-only partial chains and their separate full-root negative query
certificates. Each assembled proof independently verifies. W34 remains
INCONCLUSIVE; knot type alone supplies no negative-cone conclusion.

| Diagram input | Strict32 endpoint | Enabled endpoint | Accepted U1 macros | Query status | Nodes/pivots | Exact h |
|---|---:|---:|---:|---|---:|---:|
| braid(2,[1,1,1]), T |8|7|1|NO_POSITIVE_EULER|5/259|1|
| braid(3,[1,-2,1,-2]), F |12|10|1|NO_POSITIVE_EULER|1/676|0|
| braid(3,[1,1,1,2,2,2]), TT |17|16|1|NO_POSITIVE_EULER|16/3526|2|
| braid(2,[1]*5), T25 |15|11|3|NO_POSITIVE_EULER|7/693|1|
| braid(2,[1]*7), T27 |21|17|4|NO_POSITIVE_EULER|15/2545|2|
| braid(3,[1,-2]*4), W34 |34|31|3|INCONCLUSIVE|1/10000|unknown|

All twelve preprocessing calls used max_tree_nodes=0 and made zero LP calls.
Baseline steps are exact literal prefixes of enabled steps, with identical
original diagram source and shelling. Strict32 is enabled in both arms and is
restarted after each accepted macro; thus the figure-eight source goes from12
to11 by one U1 macro, then to10 by strict32. The driver counts one macro against
max_crushes, although these thirteen accepted macros each contain one upward
and two downward elementary moves.

The independent solver-free `replay.py` passed. It replays all14 whole-driver
results/partial chains and all6 supplied-source results, verifies every
complete negative tree and all5 assembled diagram certificates, and checks
all10 unique already-exposed root rays by original STANDARD matching,
nonnegative integer coordinates, canonical normalization, incidence Euler and
exact rank while retaining every triangle column. No LP or ray discovery is
called by this replay. Per-ray data and ranks appear in `replay.json`.

Upper bounds follow from the union of actual split tetrahedra in complete
negative trees: respectively {2}, empty, {0,10}, {7}, {10,14}. Lower bounds use
already-exposed positive root extreme rays. T has conflicts{2,6}; TT has
disjoint{0,4} and{10,14}; T25 has{2,7}; T27 has disjoint{2,14} and{0,10,11}.
All these selected rays have canonical Euler one. Original STANDARD rank
subtracts exactly the one-dimensional triangle-only kernel to obtain
Q-support nullity one. Exact finite retained-hypergraph hitting enumeration
agrees with the upper bounds. In particular h(F10)=0 follows from the single
negative unrestricted-root leaf, not from an empty observed sample.

Enabled source hashes:
- T7: 73bb6ac861256fd0ce221080a684603173b8e2d197cdfac3f1434ad577b64659
- F10: e0c4fa8d6a5a580614a48ae28047e60c8275c4b9cf2f19f717c84e8d93b89923
- TT16: 3acd081d4bf0f8081ed80b4ef5902490d0a77ff9c20d5cc3c973a0590ccb5dbc
- T25 11: df22b608289b64c4c108e87166dc573df0a6da3c0e4e5d83da355e923fad0d89
- T27 17: 754587a4f50a6df175867ec0ae6d4dd7e68bcb4470e5ba0415be29e7ca4c532b
- W34 31: 5f53366b61f16027b896868a66cee02dce1c7a21b0cbb513e4ef583d2fd44345

The old `/tmp/strict-descent-next-design/` archive remains unchanged. Its
strict32-only T25 h=3 and T27 h>=3 results concern different labelled sources.
Current source-specific improvements do not prove monotonicity under moves,
a uniform polylogarithmic h bound after U1 exhaustion, or quasi-polynomial
recognition. W34 remains a concrete unresolved capped case.

Reproduce only verification:
`python -B /tmp/fixed-u1-staged-audit/replay.py`

Re-running audit.py performs the exact20 discovery calls and overwrites its
local output; preserve this directory first if a new native revision is used.
The native source hashes in audit and replay are generation/replay provenance;
they become historical when future native files change. The manifest hashes
all retained files except itself.

Before archival freeze, handoff prose was corrected from eleven to ten unique
new exposed rays. The preceding strict32-only archive has eleven. Raw audit and
replay outputs were unchanged by this correction.
