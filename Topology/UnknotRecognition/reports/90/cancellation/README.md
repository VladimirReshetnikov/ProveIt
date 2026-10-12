# Connected cancellation profiles

This is an additive research overlay for the ProveIt unknot-recognition
project, pinned to `a28a49ee5c4145db0facbeb1e7f65cd8a2816775`. It extends
the separately supplied `unknot_cancellation_20261012` package.

## Results and scope

For a supplied one-vertex, rank-one, finite orientable torus-boundary
source, write an essential disc's edge weights as `w=b+u`, where `b` is
the absolute primitive cocycle and `u` is a nonnegative even integral
vector. Let `k` count its nonzero increments, `r` count their components
in the graph joining edges that share a tetrahedron, and `d` be the
maximum number of distinct tetrahedra incident to one global edge.

The theorem in `cluster_theorems.tex` gives complete standard-vertex
disc discovery in

`t^(r+O(1)) (C d^2)^k poly(k,B)`.

Connected supports supply local affine profiles; profiles on nonadjacent
supports can be combined independently. The exceptional case where
`supp(b)` is contained in the defect support is treated by normalized
homogeneous systems. An extreme normal ray cannot have disconnected
positive edge support, which covers this exceptional case.

The theorem does not bound `k`, `r`, or `d` on arbitrary unknot sources.
An edge can meet linearly many tetrahedra. Several vertices require a
shared cocycle/potential treatment; a fixed coherent vector is then
incomplete. All negative statuses concern only the searched class.

## Code and provenance

- `fastunknot/normal_weight_clusters.py` is the new implementation. It
  includes exact local reconstruction, disconnected profile assembly,
  the homogeneous branch, recomputation of the actual defect after
  primitive normalization, global work/support/system/combination
  limits, and independent replay of every positive disc certificate.
- `fastunknot/normal_vertex_gate.py` is an **unchanged copy** of
  `artifacts/edge_discovery/vertex_gate.py` from the incoming cancellation
  package. It is reused rather than claimed as a new contribution.
- `normal_weight_defect.py` is an incoming dependency. The pinned
  maintained repository does not yet contain it. The overlay imports
  the incoming file through `bootstrap.py`; no checkout is modified.
- Other dependencies are the pinned repository's `fastunknot` modules
  and the Python standard library. Regina 7.4 is used only by the
  optional external census.

To integrate, add the new cluster module, provide the incoming
`normal_weight_defect.py`, and copy the incoming vertex gate under the
name `normal_vertex_gate.py`. The two gates have distinct roles:
discovery chooses candidates, while the gate proves that a supplied
primitive vector is a connected essential disc. The maintained diagram
recognizer and its defaults are unchanged by this overlay.

## Reproduction

The default layout places this directory beside `ProveIt` and
`incoming_review`. For a different layout set:

```bash
export PROVEIT_UNKNOT_ROOT=/absolute/path/ProveIt/Topology/UnknotRecognition
export CANCELLATION_PACKAGE=/absolute/path/unknot_cancellation_20261012
```

Then run from this directory:

```bash
python -m unittest discover -s tests -v
python audit_disconnected.py
python audit_one_edge_inventory.py
python audit_disconnected.py --full-census
python benchmark_clusters.py
```

The optional full census uses two different Regina algorithms and can
take tens of seconds. The full benchmark is substantially longer because
it exhausts the radius-two all-support baseline through 40 tetrahedra.
Avoid concurrent compute-heavy work during benchmark runs.

## Retained counterexample

`artifacts/disconnected_disc.json` contains a fifteen-tetrahedron solid
torus and a standard vertex meridian with increments `+4` at edges `47`
and `53`. Their stars are respectively `{7,13}` and `{8}`; the support
therefore has two disconnected singleton components. The source is the
incoming obstruction after four boundary layers and the three legal
2–3 moves `(4,0), (5,0), (12,0)` in successive labels. Its isomorphism
signature is `pHKzvvPAPQMcbcdlhlhjmmmlnoohqxrorfjidicxak`.

At radius two, the one-component search exhausts without a disc, while
the two-component search finds this certificate. The incoming supplied
weight-space enumerator independently recovers the same vector. The
explicit positive witness disproves the assertion that every vertex
meridian has connected cancellation support.

An independent dense-row audit proves the stronger finite statement
`κ_V = 2` for this source: no standard vertex meridian has cancellation
support of size zero or one. The coherent vector has Euler
characteristic `-7`, and its fifteen nonzero edge weights exclude the
dependent-baseline exception for every singleton support. The active-row
theorem therefore reduces the one-edge case to offsets
`δ = -ℓ(b) / ℓ_e` that are positive even integers. The script
`audit_one_edge_inventory.py` independently constructs all dense corner
and opposite-sum hyperplanes: 119 distinct rows, 327 nonzero row-edge
incidences, and 35 distinct positive even offsets. Exactly three are
admissible, at edges `42`, `47`, and `53`, each with increment `4` and
Euler characteristic `-3`; none is a disc. The certified two-edge disc
supplies the upper bound. The full inventory and normal vectors are
retained in `artifacts/one_edge_inventory.json`.

This audit does not call the new profile producer or its sparse row
builder. It reuses the maintained cocycle and coordinate routines and the
incoming local normal decoder. The proof is an exact reproducible finite
computation, not a proof-assistant formalization or a separate generic
negative-certificate format. It needs no full vertex census and makes no
claim about the absence of one-component supports of arbitrary size.

For broader finite evidence, Regina's direct standard-coordinate tree
traversal and double-description methods return the same 821 vertex
vectors. Exactly three are meridians, with `(k,r)` equal to `(2,2)`,
`(4,2)`, and `(4,2)`. Their positive certificates are independently
replayed. The completeness of that census remains external enumeration
evidence; it is not an independently verified negative certificate.

## Tests and measurements

The focused tests compare the new candidates with exhaustive incoming
weight-space search on actual sources, check the disconnected witness,
exercise the dependent-baseline homogeneous case, compare connected
support enumeration with exhaustive subsets, test exact global limits,
propagate external cancellation, preserve input data, disable producer
routines during independent replay, reject forged certificates, and
test exact arithmetic on 8193-bit inputs.

`artifacts/benchmark.json` records paired samples, medians, observed
ranges, counters and file hashes. Radius-two timings cover complete
candidate generation, source/cocycle preparation, local reconstruction
and actual-defect filtering. They exclude vertex topology gates. The
candidate sets are compared outside timed blocks. Radius-one positive
timings include the complete queries and internal independent replay;
the incoming method uses its native component observer, while the new
method uses the polynomial rank gate. That distinction is explicitly
retained, and measured regressions are reported without omission.

The evidence fragment `search_evidence.tex` contains both benchmark
tables and their scopes. Ratios are ratios of the two arm medians, not
medians of per-round ratios. Radius-two gains use the all-support median
divided by the profile median; radius-one slowdowns use the profile
median divided by the incoming specialized one-edge median.
