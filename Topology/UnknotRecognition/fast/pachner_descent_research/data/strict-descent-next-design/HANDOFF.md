# Completed finite research slice (before U=1 native promotion)

All nine authorized discovery phases returned and are saved. No further LP
queries or ray enumeration were run. The final solver-free `replay_all.py`
passed, including fresh replay of the historical package's initial chains and
nine moves, all three new preprocessed diagram chains, the new T25 full-root
negative proof, eleven exposed root rays by original STANDARD equations, and
the three new U=1 local descents. Each JSON preserves exact source arrays,
options, labelled source SHA256, native generation pins and complete outcomes.
The native generation state is the strict32 publication at fb597741b; later
new-module additions naturally make these historical generation pins.

## Three precisely labelled diagram sources

| Input | Original/shelled/final tets | Vertex crushes | Strict32 moves | Full-root Euler outcome |
|---|---|---:|---:|---|
| braid(2,[1]*5), T(2,5) |100/88/15|20|5|NO_POSITIVE_EULER:27 nodes,7113 pivots,748 anchors|
| braid(2,[1]*7), T(2,7) |140/128/21|28|11|INCONCLUSIVE:21 nodes,10000 pivots,543 anchors|
| braid(3,[1,-2]*4), W(3,4) |160/148/34|32|3|INCONCLUSIVE:1 node,10000 pivots,6 anchors|

All preprocessing calls used max_tree_nodes=0 and made zero LP calls. All
endpoints have one finite vertex, one torus boundary, no eligible strict32
edge, and no accepted boundary peel. The latter two Euler calls stop at their
shared pivot cap. They do not establish negative canonical cones or h upper
bounds. The braid labels, not an external identification oracle, define inputs.

T25 labelled source:
`9a4614fd806ac8d6264ade566ad890c8e6f416c1534644b382fdc51de9e5b16e`.
Its 16-node complete negative tree splits only in B={0,1,4}, so h≤3. Of five
already exposed and independently verified root extreme rays, three have
disjoint conflicts {0,7}, {1,11,12}, {4,10,13}. These are capture indices
0,4,10, each with canonical Euler one. All 60 triangle columns are retained:
triangle rank59, and respective (full columns,rank) pairs (74,72),(71,69),
(75,73). Subtracting the one-dimensional triangle kernel leaves Q-nullity one
in each support. Hence h≥3 and **h(T25 endpoint)=3 exactly**. The full retained
five-edge hypergraph also has transversal number3; all105 two-subsets were
exhausted. This is a finite one-vertex, strict32-exhausted prime torus-knot
source, not a counterexample to any polylogarithmic bound.

T27 labelled source:
`bc3f7c3f0179874d5a737bc83c5b85d710fe26da22c360050fd1133c22d399d5`.
Six already exposed root rays replay. Capture indices0,7,10 have disjoint
conflicts {0,7}, {1,10,16,17}, {4,6}, canonical Euler1,3,1. All84 triangle
columns have rank83; respective (full columns,rank) are (102,100),(103,101),
(101,99). Thus h≥3 despite the inconclusive full-root query. The retained
six-edge hypergraph has a size3 hitting set; that is **not** h≤3 for this source.

W34 labelled source:
`72bde627081c0ffd995e0c5b59e00d01053c26feee76d595b75d8ad0d8fb59d9`.
The capped query exposes no positive point. No nontrivial bound on h follows.

## Independent U=1 experiment on previously published endpoints

All use zero initial cochain, method=sleep, max_upward=1,
max_nodes=256,max_work=200000,max_regions=10000,max_oracle_states=10000.
The auto cover backend selects indexed for these tiny finite controls.

| Source | Verified strict endpoint | Search nodes | Charged aggregate work |
|---|---|---:|---:|
|T8|7 tetrahedra|10|13782|
|F12|11 tetrahedra|21|56779|
|TT17|16 tetrahedra|50|117490|

Each returned endpoint has exactly one upward and two downward moves, all
transported heights remain zero, and inspect_pachner_descent independently
replays the complete source-bound packet. No disc counting or LP occurs.
New successor SHA256 values respectively:

- `73bb6ac861256fd0ce221080a684603173b8e2d197cdfac3f1434ad577b64659`
- `71b2ebc585c899c8ef911df3a8293cf096db8951274fc685d59873966c479a67`
- `3acd081d4bf0f8081ed80b4ef5902490d0a77ff9c20d5cc3c973a0590ccb5dbc`

No Euler queries, h bounds, or negative canonical-cone claims have been made
on these three new successors. There is no h-monotonicity theorem in this work.

## Proposed next experiment, not yet run

After the independent fixed-U=1 wrapper and mixed-chain integration are ready,
run the genuine whole-diagram driver on circle,T,F,TT and these three labelled
torus/weaving inputs, with max_tree_nodes=0 and the U=1 policy explicitly on.
Restart the existing vertex/peel/strict32 preprocessing after every verified
strict macro; retain full provenance and the final source. Then make exactly
one capped full-root Euler query per returned nonterminal endpoint under the
same256/10000 limits above. Compare certified source outcomes and exposed-ray
lower bounds; no elapsed-time claim until a separately frozen protocol.

This will distinguish an occasional local escape from a useful repeated
preprocessing policy. It can refute a small fixed-h conjecture at specific
simplified sources, but finite results cannot prove the missing uniform
polylogarithmic resolving-set theorem. Fixed-U first descent itself is already
polynomial and independently source-replayable; its integration is the concrete
next algorithmic step. Native implementation now belongs to the next slice.

Reproduction: commands are in MEMO.md; `python -B
/tmp/strict-descent-next-design/replay_all.py` runs only verification. Preserve
all outputs and scripts together. `manifest.json` hashes all files in this
directory except itself, and records the final replay hash.
