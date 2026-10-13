# Finite connected-sum conflict evidence

This package retains one native, diagram-authenticated two-trefoil source with
35 primitive positive incompatible root Q rays. Its retained conflict hypergraph
has transversal number exactly **5**, so the full source parameter satisfies
**h(T) >= 5**. No upper bound of 5 for the full source is asserted. There is no
complete negative canonical-cone certificate or complete recognition result.

The experiment invokes `recognize_by_crushing` directly on the entire sum.
The existing high-level `recognize` router already uses visible interlacement
factorization before its factor engines; this is not a lower bound for that
router or a claim that it must construct this combined cone.

The source comes from the closure of the three-strand braid `[1,1,1,2,2,2]`.
The native interlacement certificate decomposes its PD into two copies of the
same trefoil PD, under explicit edge-label bijections preserving every crossing
slot. Native exterior construction produces 120 tetrahedra, shelling leaves 114,
and 24 vertex-reduction crushes leave a one-vertex 23-tetrahedron exterior.
The exact labelled source digest is:

`825247bfc387213d7cc965a33018a448043469eecf0a9edd3ce8d7a1b5fcb6f9`

A fresh run with `unlayer_boundary=True`, the conflicts candidate policy, and
zero tree-node/pivot/anchor allowances retains the same labelled endpoint and
same 24 crushes. The independent v2 chain replays. Its two boundary faces are
`(17,0)` and `(20,0)`, so no supported exposed inverse layer exists. This says
nothing about all possible topological simplifications or future positive
normal crushing. The control is a partial `REDUCED` chain.

## Solver-free replay

Run from `Topology/UnknotRecognition/fast` using ordinary Python:

```sh
PYTHONPATH=. python -m conflict_composition_research.replay --output ../synthesis/data/conflict-composition-audit.json
PYTHONPATH=. python -m unittest conflict_composition_research.test_replay -v
```

A saved audit can be checked against a newly computed replay with
`--check-evidence PATH`. Fresh audit pins cover every native Python file and
every package input/source, including compressed historical records. Running
Python with `-O` disables the research assertions and is unsupported.

The replay uses no Regina, LP solver, ray search, or Q-cycle elimination.
It validates the original labelled triangulation and both complete crushing
chains, rebuilds original STANDARD matching equations, computes exact rational
ranks, evaluates formal Euler by cell incidences, and checks canonical peeling
and primitive Q gcd. With all 92 triangle columns and each ray's positive Q
columns, the matching nullspace has dimension2; its triangle-only kernel has
dimension1. The projected Q support therefore has nullity1. The rays are
extreme in the full source cone, not merely in an incompletely sampled sector.

Every four-element subset of all 23 tetrahedron labels misses a retained
conflict edge: 8,855 exact checks. A seven-ray core also has a short proof:

| Ray | F | Conflict set |
|---|---:|---|
| 5 | 1 | 3,4 |
| 6 | 1 | 5 |
| 7 | 1 | 7,12,17,21 |
| 11 | 1 | 10,11,14 |
| 17 | 2 | 12,14 |
| 19 | 1 | 7,14,18,19 |
| 20 | 2 | 11,16,19 |

The first two rows require two distinct choices outside the last five sets.
For the last five, any pair must contain 12 or 14. With 12, its other member
would need to lie in `{10,11,14} ∩ {7,14,18,19} ∩ {11,16,19}`, which is empty.
With 14, its other member would need to lie in
`{7,12,17,21} ∩ {11,16,19}`, also empty. Thus three further choices are needed.
The set `{3,5,7,11,14}` hits all 35 retained edges. It is only a retained-family
upper bound. A four-edge disjoint packing is also retained, but is weaker.

## Historical discovery and reproducibility

`data/provenance.json` records exact original-byte SHA256 values and deterministic
compressed-file hashes. JSON archives decompress to their original scratch
bytes. Historical native hashes are left intact inside each generation phase;
they are not relabelled as current-source hashes. The default fresh replay
checks mathematical data under its separately recorded current pins.

`data/generation/` preserves the entire state, both chain schemas, all 35 raw
coordinate arrays, five candidate refutations (including partial trees/dual
caches), every bounded query's configuration/caps/outcome, and original scripts
and stdout. The first full search exhausted 5,000 pivots. Two deterministic
20-query anchor batches supplied additional rays. Four size 4 candidates and
one size 5 candidate were refuted. None is a negative-cone certificate.
The final candidate `{3,5,7,11,12}` was refuted by`{14,18,19}`.
No discovery attempt was silently promoted to a conclusive negative result.

To repeat historical discovery, unpack all archived generation JSON into a
new scratch directory alongside copies of its `.py` scripts. Use the pinned
historical native checkout if exact solver trajectory reproduction matters;
run with `fast/` as working directory and `PYTHONPATH=.`. The recorded sequence:

```sh
python SCRATCH/fixtures.py
python SCRATCH/prepare.py tt --seconds 20
python SCRATCH/search_phase.py tt --seconds 20 --nodes 128 --pivots 5000
python SCRATCH/diverse.py tt --seconds 20 --queries 20 --seed 20261013
python SCRATCH/candidate_phase.py tt --B 3,5,7,10 --seconds 20 --pivots 10000
python SCRATCH/candidate_phase.py tt --B 3,5,10,12 --seconds 20 --pivots 10000 --cache-from SCRATCH/tt-candidate-3-5-7-10.json
python SCRATCH/candidate_phase.py tt --B 3,5,11,12 --seconds 20 --pivots 15000 --cache-from SCRATCH/tt-candidate-3-5-10-12.json
python SCRATCH/candidate_phase.py tt --B 3,5,12,14 --seconds 20 --pivots 15000 --cache-from SCRATCH/tt-candidate-3-5-11-12.json
python SCRATCH/diverse.py tt --seconds 20 --queries 20 --seed 20261014
python SCRATCH/candidate_phase.py tt --B 3,5,7,11,12 --seconds 20 --pivots 15000 --cache-from SCRATCH/tt-candidate-3-5-12-14.json
python SCRATCH/unlayer_control.py
```

The archived scripts' original scratch paths, seeds and absolute cache-origin
references are historical provenance. The commands above substitute the chosen
new scratch path. Cooperative wall limits are exploration limits; neither these
records nor their stdout constitute a timing benchmark. TF and FF fixtures were
checked only at the diagram-factor level, not by source/ray exploration.

`data/gluing-design/MEMO.md` preserves the earlier mathematical design notes and
exact missing transport hypotheses. It is not an asymptotic theorem or evidence
that copied summand rays remain extreme after gluing. A growing lower-bound
family, survival through more general simplification, and a useful upper bound
on the canonical-negative endpoint parameter remain open.
