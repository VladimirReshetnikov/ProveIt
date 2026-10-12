# Incoming audit and joint forest theorem

Prepared against ProveIt commit `8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`.
This is working material for the parent article, not an independent delivered report.

## Audit scope and overlap

The ten current incoming ZIPs were read through Git into isolated scratch directories.
No incoming patch was applied and no imported evidence file was changed. The review
covered top-level READMEs, abstracts, theorem statements, relevant geometric proofs,
claim boundaries, and research agendas. It is a targeted overlap audit, not a full
independent proof audit of every imported manuscript.

| Incoming manuscript | Existing substantive results | Relevant limitation |
| --- | --- | --- |
| Cographic Persistence | Nonseparating disjoint surface batches are independent sets of a chamber graph's cographic matroid; weighted-orbit chamber recovery; optimal retained reward via an MST; dual-loop persistence; exact causal rebuild recurrence and reverse amplification. | This concerns surface retention and dependency resets. It does not select 2/3 cancellation forests or couple them to raw 1/2 cancellation. Its geometric route exporter remains absent. |
| Disconnected Tile Kernels | Polynomial kernel for arbitrary disconnected repeated graph tiles, avoiding a global permutation period; stable powers, channel cycles, exact marked signatures, contextual replacement, succinct lifts. | An abstract graph operator, with no native source geometry, ball authentication, embedded noose transport, or 3-handle reduction. |
| Genus Budgets and Native Interfaces | Unused-cocore Euler/genus budget, rooted absorption of ball pieces, source-bound initial torus compiler, local tetrahedral admissibility, native first returns and exact gap/fibre data, unmarked reconstruction theorem. | Its 2/3 queue is the maintained INITIAL triangulation reduction; later cut cores with 3-handles remain outside its terminal consumer. Patterned reconstruction remains an obligation. |
| Modular Morse Certificates | Polynomial verification and fixed-template synthesis of synchronized modular ranks for supplied interval matchings; exponential fixed-coordinate affine-rank obstruction; relative products and authenticated regular PL product lifts. | It does not authenticate an arbitrary native raw CW packet, regularize source identifications, discover a matching, or cancel native 3-handle cores. |
| Moment-Coded First Returns | One scalar weighted census for terminal pairs, lengths and finite-group transport; exact moment decoding; active holonomy test; refinement/coarsening and candidate-reservoir reuse. | No native geometric 2/3 operation or boundary-pattern transport through cancellation. |
| Saturated Bundle Cancellation | One residual relation per saturated base; even private cocore columns; exact no-fill column peeling and timestamp verification; native unmarked census at 85/106 cases; conditional observer and seam-repair bounds. | Ten cut cores with 3-handles remain excluded. Seven are reported positive by the external small-input oracle. Their explicit research agenda asks for safe 2/3 cancellation. |
| Scalar Separators | Exact two-slope continuation at one-dimensional matching-cone interfaces; source compilation; no-new-rays theorem; local intrinsic-dimension bounds; a two-port exponential cone-message obstruction. | Surface-discovery module. No forest-choice or later handle cancellation theorem. |
| Unknot Hierarchy Kernels | Clustered defect search, unsaturated interval-bundle relative handle theorem and unmarked census, disconnected through-component repetition kernels and sharp connected cutoffs. | Genuine saturated relations, marked transport, and unsupported three-handles remain limitations. |
| Sparse Cut Grammars | Sparse marked small-cut responses, degree-k joins, polynomial connected-grammar evaluation at fixed threshold, bounded-component extension, independent response replay and addresses. | No native faithful graph producer, embedded boundary noose/disc transport, or 3-handle operation. |
| Stopping Cores | Complete rectangular positive raw cancellation is unit-column peeling; canonical stopping obstruction; exact positive passenger DAG transport; source-bound saturated bundle joint census at 85/106. | Eleven raw stalls and ten 3-handle exclusions remain. It explicitly asks for source-forest exchanges, 3-handle cancellation, and geometric marked-pattern transport. |

The maintained `synthesis/data/core-three-handle-probe.py` is relevant prior work.
It already recovers candidate source endpoints, deletes rooted 2/3 pairs, and
compares candidate downstream censuses. Its own docstring explicitly says that
independent source replay is missing. The present joint forest theorem extends
that line by changing the forest to control the surviving occurrence rows.

## 1. Formal input and the two graphs

Fix a geometric primal forest quotient. Let E be the remaining 2-handle labels,
V the 3-handle labels, and C the nonforest 1-handle labels. For each e in E the
source provides zero, one, or two 3-handle endpoint OCCURRENCES, and an unsigned
nonnegative integer row a_e on C. Missing endpoints mean exterior boundary.
Two equal occurrences must be retained; they form a loop, not a singleton.

Introduce a boundary root rho. Complete the endpoint list of each e to length
two by rho. This gives a multigraph G on V union {rho}, with loops allowed.
Multiple source boundary components may all be identified with rho: a tree in
this quotient lifts to a forest with one boundary root in each component.

Define capped rows b_ec = min(2,a_ec). Every singleton-column predicate is
unchanged by this saturation, on every row subset. Let

    D = {e : sum_c b_ec > 2},    E0 = E minus D.

The implemented strategy requires every D-row to be deleted by 2/3 cancellation.
It does not assert that retaining a longer row prevents raw cancellation.
Indeed one row (1,1,1) peels immediately. This explicit restriction is essential.

For each e in E0 form an edge h_e on C union {omega}:

* two distinct unit entries join their two columns;
* one unit entry joins its column to omega;
* one entry at least two gives a loop at its column;
* an empty row gives a loop at omega.

The resulting multigraph is H. The two graphs share EDGE LABELS, but their
vertices and their meanings differ. All examples below are combinatorial
instances. We make no claim that arbitrary choices of G and H are realized by
a 3-manifold handle system or satisfy its chain-complex constraints.

## 2. Dual deletions are rooted spanning trees

**Lemma.** A full sequence deleting a 2-handle incident exactly once to a live
3-handle, together with that 3-handle, exists exactly when G is connected.
The deleted edge sets of such sequences are precisely the spanning trees of G.

**Proof.** For a spanning tree rooted at rho, process vertices after their parent
has already been deleted (breadth-first order suffices). The edge joining a
vertex v to its parent then has exactly one live endpoint, v. Removing the pair
is legal in the stated graph model. Conversely, orient every edge of a supplied
complete deletion trace from its deleted vertex to its other endpoint. The other
endpoint is either rho or a vertex deleted earlier. Thus repeatedly following
these directed edges reaches rho. Exactly one edge is chosen for each vertex,
so the chosen edges are a connected graph with |V| edges on |V|+1 vertices,
hence a spanning tree. A doubled endpoint is not legal at its sole live vertex,
so a loop can never enter such a tree. QED.

This is an occurrence theorem. Turning it into a geometric cancellation theorem
requires the native source authentication supplied by the adjoining development.

## 3. The short-row graphic criterion

**Lemma.** For S contained in E0, complete unit-column peeling of the rows b[S]
is equivalent to H[S] being a forest.

**Proof.** A nonground vertex's degree in H[S] equals its corresponding column
sum, with loops counted twice. If H[S] is a forest and has an edge, a tree
component with edges has at least two leaves. At most one is omega, so there
is a nonground leaf. Its column sum is one and the incident row can be peeled.
Deleting that row removes its graph edge and leaves a forest. Induction deletes
every row. Conversely, a cycle's edge set has degree zero or two at each
nonground vertex; a loop has the same property. These rows form a nonempty
stopping set. No unit-column deletion can remove its first row. Thus a cyclic
H[S] cannot peel completely. QED.

By the previously supplied stopping-persistence theorem, the same forest
condition is also equivalent to full positive raw cancellation in the exact
specified model. That extension uses the earlier theorem; it is not attributed
to the new forest-planning implementation.

## 4. Joint forest criterion and forced long rows

If G is disconnected, full rooted 2/3 deletion is impossible in this model.
If D contains a cycle in G, no dual spanning tree can contain all of D. In the
remaining case contract D in G and call the connected result G'. Its edge set
is E0; contraction may create loops or parallel edges and they must be retained.
Write r_G' and r_H for graphic rank, including all fixed isolated vertices.

**Theorem.** The following conditions are equivalent:

1. There is a spanning tree F of G containing D such that all surviving rows
   E minus F admit complete positive raw cancellation.
2. E0 is the disjoint union of a forest of G' and a forest of H.
3. For every Y contained in E0,

       |Y| <= r_G'(Y) + r_H(Y).

Moreover a deterministic polynomial-time algorithm produces either a full
2/3-plus-1/2 schedule or a subset Y violating this inequality.

**Proof.** (1) gives (2) by taking F minus D in G' and using the short-row
lemma on its complement. For (2) to (1), extend the G'-forest to a spanning
tree of G' by repeatedly moving an H-forest edge that joins different current
G'-components. Such an edge exists until G' is spanned, since it is connected.
Removing edges preserves the H-forest. Undo the contraction of D and use the
rooted deletion lemma and then the short-row lemma. The necessity of (3) for
(2) follows by intersecting a forest partition with Y and summing the two rank
bounds. Sufficiency, together with the promised algorithm and certificate, is
proved constructively in the next section. It is the two-graphic specialization
of classical matroid partition, credited below. QED.

The equivalent matroid-intersection formulation asks for a basis of the
cographic matroid of G' which is independent in the graphic matroid of H.
The implementation uses two-graphic partition because its failure witnesses
have particularly direct component-count verification.

## 5. Self-contained augmenting-path proof

Maintain disjoint edge sets I_0,I_1, forests in G',H respectively. Initially
both are empty. An edge is unassigned if it belongs to neither set. In the
exchange digraph, for e outside I_i, e is an i-sink if I_i plus e is a forest.
Otherwise its unique fundamental circuit consists of e and the forest path
between its endpoints. Add an arc e to f for every path edge f in I_i.
A loop's forest path is empty and it has no such exchange arc.

Start breadth-first search from every unassigned edge. If a sink is reached,
take a shortest source-to-sink path e_0,...,e_l. Assign the last edge to its
sink forest. For each j<l assign e_j to the original forest of e_{j+1}.
Exactly one additional edge has now been assigned.

Here is a proof that each resulting color class is a forest; it also states
why a SHORTEST path is required. Represent each graph edge by its endpoint
incidence vector over F_2. Forest edge vectors are linearly independent.
For an incoming edge e_j, j<l, its vector is the sum of the vectors on its
fundamental forest path. The coefficient of e_{j+1} is one. For any later
edge e_{k+1} removed from that same forest, with k>j, its coefficient is zero:
otherwise e_j to e_{k+1} would be an exchange arc, yielding a strictly shorter
source-to-sink path. Consequently the matrix of incoming-edge coefficients
on removed forest edges is triangular with diagonal one, in path order.
It is invertible. Replacing these removed edges by the corresponding incoming
edges therefore preserves linear independence and the old span. Earlier path
vertices cannot themselves be addable to a forest, since that would be a
shorter sink path. The terminal edge, in its sink forest, lies outside the
old span and raises that forest's rank by one. Thus both color classes remain
forests, proving the augmentation rule.

If no sink is reachable, let Y be the set of reached edges and U the set of
all unassigned edges. Every U-edge lies in Y. For each i and every e in
Y minus I_i, its fundamental path lies in I_i intersect Y: all its exchange
arcs have been explored. Therefore I_i intersect Y spans Y in its graph and

    r_i(Y) = |I_i intersect Y|.

It follows that

    |Y| - r_0(Y) - r_1(Y) = |U| > 0.

This is the promised failure certificate. More strongly any union of two
forests contains at most |E0 minus Y|+r_0(Y)+r_1(Y) = |E0|-|U| edges. The
current partition attains this bound, so it is maximum. If the search assigns
all edges, it gives the desired full partition. This proves both the rank
criterion and the completeness of the deterministic algorithm.

There are at most m=|E0| augmentations. For each search the implementation
rebuilds the two forest adjacencies and explores at most m edge vertices.
Each fundamental path is found by one ordinary graph traversal. Sorting path
edge labels gives the conservative structural bound

    O(m^2(v+m) + m^3 log(m+2)),

where v=|V(G')|+|V(H)|. Encoding, comparison, and callback work remain
polynomial in the full bit-size of the supplied data. Memory is linear in
the explicit source incidence and graph sizes. No binary multiplicity is
expanded: saturation is a single integer comparison per nonzero input entry.

## 6. Exact residual deficiency

Put

    d = max_{Y subset E0} (|Y|-r_G'(Y)-r_H(Y)).

The empty subset ensures d>=0. The augmentation proof shows that maximum
two-forest union size is m-d and produces a Y attaining d when d>0.

**Theorem.** Among all dual spanning trees F containing D, the least cycle
nullity of H[E minus F] is exactly d. The planner produces a tree attaining
it and independently checkable witnesses for both bounds.

**Proof.** For any dual spanning tree F, let J be a maximum forest in its
H-residue S. Then (F minus D) union J is a union of two disjoint forests,
so |F minus D|+r_H(S)<=m-d. Since |F minus D|+|S|=m, this gives
|S|-r_H(S)>=d.

For the reverse bound, start with a maximum partial partition I_G,I_H of
size m-d. Every unassigned edge has its G'-endpoints in one I_G-component,
since otherwise it would be immediately assignable and the partition would
not be maximum. Hence I_G union I_H spans G'. Extend I_G to a spanning tree
T using I_H edges only. The remaining I_H edges form an H-forest J in the
residue S=E0 minus T. Exactly d unassigned edges also remain in S, so
|S|-r_H(S)<=|S|-|J|=d. Equality follows. Lifting T across D gives F. QED.

Equivalently d is the least number of ADDITIONAL ARBITRARY ROW DELETIONS that
would make a residue peelable, optimized over the allowed dual trees. Such
extra deletions are not geometric cancellations and are never applied by this
prototype. The number is an exact diagnostic of the specified matrix model.
An occurrence forest and the d unassigned rows are retained in every rank
obstruction certificate, with an optimal dual tree and a legal 2/3 trace.

## 7. Why the general raw problem is not matroid intersection

Consider four binary rows

    a=(0,0,1), b=(0,1,1), c=(1,1,0), d=(1,1,1).

The row sets I={c,d} and J={a,b,c} both peel. Yet |J|>|I|, and neither
I union {a} nor I union {b} peels: every nonzero column sum in either enlarged
set is at least two. Thus the family of generally peelable row subsets
violates matroid augmentation. Already a single row of length three destroys
the unrestricted graphic claim. It would be incorrect to invoke matroid
intersection on the general raw-peelability family without an additional
representation theorem.

A second scope example is a single row (1,1,1), no three-handles, and a dual
boundary loop. It peels directly, but the restricted strategy forces its row
into a dual spanning tree, which is impossible. Its certified refusal therefore
does not mean that no raw cancellation exists, let alone that the source is
not a handlebody. The independent tests retain this example.

## 8. Code and evidence

New source files, and no existing dispatch changes:

* `fast/fastunknot/core_forest_exchange.py`
* `fast/fastunknot/core_forest_exchange_verify.py`
* `fast/tests/test_core_forest_exchange.py`

The API is `plan_forest_exchange(three_handles, endpoints, occurrences,
check=...)`. The independent replay API is `verify_forest_exchange` with the
same source arguments and the supplied certificate. Positive proofs carry
the dual forest, ordered 2/3 pairs, and ordered 1/2 unit-column pairs. Negative
proofs certify a boundary-disconnected subset, a forced-row dual cycle, or an
exact rank deficiency and an optimal residual tree. A verified negative proof
is not a negative topological result.

The verifier imports no producer code. It obtains graph ranks by a separate
component traversal, uses the rank-contraction identity instead of the
producer's explicit contraction, replays 3-handle endpoint occurrences, and
checks 1/2 schedules by source timestamps rather than running a leaf queue.

The retained suite has twelve named methods. It includes 12,350 exhaustive
labelled small dual/occurrence instances, 1,200 seeded general-row cases,
exhaustive tree optimization of residual deficiency on those instances,
loops, repeated edges and crossings, forced contractions, the augmentation
counterexample, rank and schedule mutations, producer-disabled replay,
cooperative interruption, source immutability, and 16,385-bit labels/counts.

## Classical source

Jack Edmonds and D. R. Fulkerson, *Transversals and Matroid Partition*,
Journal of Research of the National Bureau of Standards, Section B, 69B(3),
147–153 (1965). Theorem 1c, p.150, is the distinct-matroid partition criterion;
section 5 explains forced-subset contraction. Original publication PDF:
https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf

The graph-matroid framework and partition theorem are classical. The proposed
contribution is their precise coupling to source endpoint deletion and capped
geometric occurrence peeling, the restricted forced-row strategy, the exact
diagnostic distance, and independently replayed research implementation.
