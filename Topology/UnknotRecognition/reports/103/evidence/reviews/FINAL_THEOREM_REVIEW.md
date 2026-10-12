# Final adversarial theorem review

Reviewed 12 October 2026 against the current working files, based on ProveIt
commit `8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`.

## Verdict

The universal source-tree reduction is mathematically sound for the authenticated
native normal-cut construction, provided the article states and proves the
relative separation lemma below. The abstract joint-forest and exact-deficiency
theorems are also sound. **There is, however, an important additional theorem:
chain-complex compatibility substantially removes the forest-choice optimization
in the geometrically authenticated short-row regime.** This should be central to
the article. Abstract instances where one forest succeeds and another fails must
not be presented as geometric improvements without an actual source realization.

No production code was edited in this review.

## 1. Top cancellation: direction and precise relative claim

Let the current 2-handle be `h = D^2 x I`. Suppose one belt disk belongs to a
3-handle ball `B`, with multiplicity one, and the other belt disk is on the current
exterior boundary. Let `R` be the union of all other handles. Then `h union B` is
a ball: the two balls are glued along a disk. Its intersection with `R` is the
lateral attaching annulus of `h`, joined along one boundary circle to the disk
complementary to the selected belt disk in `partial B`. This intersection is an
embedded disk. Thus the current manifold is `R` with a ball attached along a
boundary disk, and is homeomorphic to `R`.

This gives exactly the implemented direction: grow the rooted region out from
the boundary, cancel the parent before its child, and expose the other cap disks
of `B` as new exterior disks. It does not join two boundary components. Identifying
all boundary ends with one graph root is only combinatorial bookkeeping.

The multiplicity condition is essential. A 2-handle with both belt disks incident
to the same live 3-handle has two contacts. It is not the ball-along-a-disk case.
Both planner and replay retain this multiplicity and reject such a loop.

If a compact marked set `P` is disjoint from the ball and its attaching disk,
choose the collar used to remove the ball disjoint from `P`. The homeomorphism
then fixes `P` pointwise, including the parametrizations of marked rectangles.
It need not, and generally cannot, fix every remaining lower handle pointwise:
some collar of the attaching disk must move. This distinction should be explicit.

The surviving lower attaching records nevertheless remain verbatim. The reduced
presentation is literally the union of undeleted handles, with the same 0/1
handles and the same attaching maps of every surviving 2-handle. Its homeomorphism
to the original manifold is a separate assertion. Do not justify unchanged
records by claiming an identity on the entire lower skeleton.

## 2. Why the native ports are separated

Location on 0/1-handles alone would not prove relative preservation: a 3-handle
attaching sphere includes patches on 0/1-handles. The required stronger fact is
available from the actual source construction, but must be explained.

Use the metric cut along the normal surface, so the two local sides of each
normal disk are distinct boundary copies. Choose the usual dual regular
neighborhoods of source vertices and edge gaps. Every selected product prism,
face strip, and edge-cap family uses a strict interior stack gap. It therefore
avoids a sufficiently small source-vertex neighborhood. Its intersection with
any source edge, when nonempty, lies in a gap between two consecutive normal
intersection points, never in either extreme gap. A product region not meeting
the edge can be kept away from a sufficiently small neighborhood of that edge.

Consequently these product pieces can be realized disjoint from the closed
source-vertex 3-handles and exceptional end-gap 2-handles. Adjacent gaps that met
the same normal disk before cutting meet different boundary copies after the
metric cut; that local distinction is needed here. It remains valid for a
one-sided global normal surface. Finite PL collar choices and simultaneous
rounding then give the same separation for the recorded interface rectangles
and for collars of the cancellation disks.

This is a lemma about a compatible realization of the authenticated source
charts, not about an arbitrary labelled matrix. Its verification is encoded by
the strict rank ranges and source incidence maps; it does not require expanding
the multiplicities. The article should state that the fixed marking consists of
these interfaces (or further markings certified disjoint from the support).
It should not assert preservation of arbitrary curves on the whole cut boundary.

I checked this against both `normal_parallelity_geometry.py` and its independent
`normal_parallelity_reference.py`: product ranks are strict interior ranks;
exceptional core 2-handles have ranks `0,w`; the remaining core ports have their
source carriers reconstructed independently. The top replay alone is not this
geometric authentication. The enclosing version-6 verifier correctly authenticates
both original source proofs before interpreting the top trace.

## 3. Universal source tree

Choose a source primal forest rooted at the boundary vertices, with one boundary
root per component. Process interior vertices in any parent-before-child order.
For a child's parent edge of normal weight zero, the sole exceptional gap joins
the child to its already removed parent or an old boundary vertex. For positive
weight, the child-adjacent extreme gap joins the child directly to the new cut
boundary. Hence every selected pair satisfies Section 1.

Distinct source parent edges give distinct selected handles. A parent edge of an
interior vertex is not a boundary edge. Self-loop edges cannot be tree edges.
The empty vector, repeated global vertices, multiple boundary roots and one-sided
normal components introduce no additional obstruction. The template uses only
source labels, and specialization uses endpoint ranks symbolically.

The implementation reflects this argument. `verify_source_top_tree` checks exact
source endpoints and parent precedence without calling the BFS compiler;
specialized proofs undergo independent endpoint replay. One scope distinction:
the mathematical theorem works for connected compact finite 3-manifolds with
nonempty boundary, whereas the maintained `_prepare` gate accepts exactly one
torus boundary component. State the implemented domain separately.

## 4. Abstract graph and deficiency theorems

The supplied abstract theorem and shortest augmenting-path proof are correct.
In the row graph, a nonempty forest has a nonground leaf; a cycle, including a loop
or a parallel-edge cycle, survives unit-column peeling. All loops must count two
incidences. Capping entries at two preserves singleton-column predicates but
does not in general preserve parity.

For the original abstract strategy, let `D0` be the rows of capped length greater
than two. If `D0` is a cap-graph forest, contract it. With `E0 = E minus D0`, the
rank criterion is

    |Y| <= r_(G/D0)(Y) + r_H(Y)  for every Y subset E0.

The corresponding optimum is

    d = max_Y (|Y| - r_(G/D0)(Y) - r_H(Y))
      = min_(F spanning tree, D0 subset F)
          (|E minus F| - r_H(E minus F)).

The exchange implementation and independent verifier establish both bounds:
the reached set gives the rank witness; the maximum partial partition extends
to a cap spanning tree using occurrence-forest edges; the residual occurrence
forest and unassigned rows attain the defect. The F2 triangular exchange proof
correctly uses a shortest augmenting path. The empty case, forced contraction,
loops, isolated columns and disconnected cap graph are handled consistently.

These are exact assertions about the specified restriction, not the unrestricted
raw cancellation problem. A longer row can peel, and a refused graph certificate
is not a negative handlebody or unknot certificate. The deficiency counts extra
arbitrary row deletions; it does not authorize them as geometric moves.

## 5. New compatibility theorem: genuinely short geometric rows

Let a geometric handle core have `m` 2-handles and `q` 3-handles. Contract a fixed
valid 0/1-handle forest. Let `A` be the UNSATURATED unsigned occurrence matrix,
with rows indexed by 2-handles and columns by the remaining 1-handles. All matrices
in this section are over `F2`. Let `B` be the `m x q` cap-incidence matrix, one
column per 3-handle, counting both occurrences of a repeated endpoint. Thus

    partial_2 = A^T,   partial_3 = B,   A^T B = 0.

The last identity is a necessary consequence of a genuine chain complex. The
reduced incidence matrix of the cap graph `G` is `B^T`, with the exterior root
omitted. Its cycle space is `ker(B^T)`. Assume every 3-handle reaches the exterior,
so `G` is connected and `rank B = q`.

**Theorem.** If every raw row has length at most two, then for every cap spanning
tree `F`,

    r_H(E minus F) = r_H(E),
    |E minus F| - r_H(E minus F) = m - q - r_H(E).

In particular, complete raw unit-column peeling of one such residue is equivalent
to complete peeling of every such residue. Choosing a different cap tree cannot
improve this residue's occurrence-graph nullity.

**Proof.** The reduced incidence representation of `H` is `A^T`: one occurrence
is an edge to the ground, two distinct occurrences are an ordinary edge, and a
double occurrence or empty row is a loop represented by zero. The chain identity
gives `col(A) subset ker(B^T)`. Restriction to the coordinates `E minus F` is
injective on `ker(B^T)`: a cycle supported entirely on the forest `F` is zero.
It is therefore injective on `col(A)`, and preserves its dimension. This is
precisely the asserted equality of graph ranks. Since every tree has `q` edges,
the nullity formula follows. QED.

Thus compatible examples have the cycle/cut orthogonality missing from arbitrary
two-graph inputs. The abstract min-max is valid, but native choice gains in this
subclass cannot be inferred from abstract examples.

## 6. Forced-set theorem, including saturation and homology

For arbitrary raw rows form the mandatory set

    D = {rows of capped length > 2}
        union {empty rows or rows with exactly one nonzero entry >= 2}.

The second set consists of ALL occurrence-graph loops. None can survive a
completely peelable short-row residue. This addition is logically forced by the
restricted strategy, not a further loss of completeness within that strategy.
Every remaining row is now genuinely a single unit entry or two distinct unit
entries. In particular, its raw parity equals its capped parity.

**Theorem.** Suppose `D` is a forest of the connected cap graph. Put `k=|D|`,
`E1=E minus D`, and let `H1` be the occurrence graph on `E1`. For EVERY cap spanning
tree `F` containing `D`,

    |E minus F| - r_H1(E minus F)
      = (m-k) - (q-k) - r_H1(E1)
      = dim H_2(core; F2).

Consequently the restricted short-row strategy admits a complete geometric
cancellation certificate exactly when `D` is a cap forest and this second Betti
number is zero. If `D` is a forest, one arbitrary spanning-tree extension suffices
to decide the strategy. There is no need to optimize over extensions.

**Proof of contraction compatibility.** Let `Q` have one column for each component
of `G[D]` not containing the exterior root; its vertex coordinates are constant
one on that component and zero elsewhere. Then `B_D Q=0` and
`B_E1 Q` is the reduced incidence matrix of `G/D`, transposed. Multiplication of
`A^T B=0` by `Q` therefore gives

    A_E1^T (B_E1 Q) = 0.

The theorem of Section 5 applies to `G/D,H1`. It proves the first equality and
independence of `F`.

**Proof of the homology equality.** Because `D` is a forest, `B_D` has full row
rank `k`. Choose a right inverse `R`, so `B_D R=I_k`. Multiplying the original
chain identity by `R` gives

    A_D^T = A_E1^T B_E1 R.

Thus the deleted column maps of `partial_2` lie in the span of its remaining
column maps, and `rank A = rank A_E1 = r_H1(E1)`. Since `rank partial_3=q`,

    dim H_2 = dim ker(partial_2) - rank(partial_3)
            = m - rank A - q.

This is the claimed quantity. The forest-peeling equivalence now proves the
complete-cancellation assertion. If `D` is cyclic, no cap spanning tree can
contain it and the strategy is impossible. QED.

The homology assertion also works for several core components with boundary.
The single formal exterior root combines their cap graphs without identifying
any topological points; the 3-handle columns remain independent. It does not
generalize unchanged to closed components with nonzero `H3`.

Vanishing `H2` is not, by itself, a handlebody criterion. Sufficiency here relies
on the geometric source, mandatory-forest hypothesis, genuinely short surviving
rows, and actual cancellation theorem. The restricted strategy can fail on a
handlebody. No general topological verdict follows from refusal.

For the older abstract defect with only `D0` forced, odd single multiplicities
at least three deserve particular care: saturation turns their nonzero parity
columns into zero loop columns. They break the direct incidence-chain identity.
After every occurrence loop is forced into `D`, this problem disappears. If `D`
is a forest, its extension attains the homological lower bound, so the original
abstract minimum defect is also `dim H2`. When `D` is cyclic, abstract defect
optimization can remain a diagnostic, but no complete short-row certificate is
possible.

## 7. Recommended article positioning

1. Present the uniform relative top-handle template as an implemented native
   advance. Credit Jackson's existing unmarked 3-handle removal lemma.
2. Preserve the exact abstract matroid theorem and certificate implementation,
   clearly scoped to supplied endpoint/occurrence data.
3. Make Sections 5–6 a principal structural theorem: geometric compatibility can
   collapse an apparently substantial optimization to a single tree extension
   and a graph-rank/peeling check. This also explains why unconstrained abstract
   examples can mislead native algorithm design.
4. Distinguish the default universal source tree from a tree containing the
   mandatory set. Arbitrary universal templates need not contain `D`; for this
   restricted strategy, first extend `D` or use its contracted rooted graph.
5. Continue to separate local polynomial verification/reduction from normal
   surface discovery, hierarchy depth, and arbitrary marked transport. None of
   the reviewed results establishes the announced global quasipolynomial bound.

## Reviewed files and independent cross-check

Read `core_audit/CORE_TOP_AUDIT.md`, `incoming_audit/forest_exchange_theory.md`,
the three `core_top_*` modules, the two `core_forest_exchange*` modules,
`normal_parallelity_geometry.py`, `normal_parallelity_reference.py`,
`normal_surface_geometry.py`, `normal_cut_handlebodies_verify.py`,
`core_handlebody.py`, and the two new top-reduction/template test modules.

The incoming-audit agent independently confirmed the compatibility argument and
checked `A_raw^T B=0` on five actual source fixtures, reconstructing uncapped
cycle counts and endpoint multiplicities. The core-audit agent is extending
these checks to the native corpus and comparing tree residues with the binary
second Betti number. Those computational checks support implementation alignment;
the proofs above do not depend on their outcomes.
