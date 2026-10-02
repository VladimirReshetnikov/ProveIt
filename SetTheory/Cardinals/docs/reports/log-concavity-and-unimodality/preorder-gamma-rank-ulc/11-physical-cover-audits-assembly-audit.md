# Independent audit: rank ULC for a physical cover of size at most three

Date: October 1, 2026. Verdict: **APPROVED**.

The theorem in `../three-core-internal-extension/PHYSICAL_COVER_THREE_ULC.md`
is correct: every finite loopless directed relation whose underlying undirected
graph has a vertex cover of size at most three has a Boolean endpoint-support
rank polynomial that is ultra-log-concave at its actual surviving degree, for
arbitrary independent nonnegative tail and head activities. Neither transitivity
nor an orientation restriction is needed. Opposite arcs and directed cycles are
allowed.

This is an ordinary support-counting and algebraic extension of the previously
approved **computer-assisted** three-core bipartite boundary theorem. The new
steps require no further finite classification. The resulting theorem is not
being presented as a wholly nonenumerative proof, because its boundary premise
retains the audited 48-type/17,376-graph dependency.

## 1. Exact support decomposition

Fix a physical cover `C={0,1,2}` and independent exterior `I`. Every edge meets
`C`, so every physically disjoint matching has at most three edges. A size-two
matching either has two cross edges, using two core vertices, or one internal
and one cross edge, using all three core vertices. Two internal edges would
require four distinct core vertices and are impossible. These alternatives are
distinguished by the endpoint support itself, so no support is counted in both
classes. A size-three matching has three cross edges: an internal edge would
leave only one core vertex for two other disjoint edges.

Consequently the producer's identities

    gamma_1=A+E, gamma_2=B+H, gamma_3=c

hold for supports counted once, regardless of how many witnesses any support
has. All core role activities remain inside `a_i,b_ij,c,h_ij,H`; none are
silently identified or factored out.

If the physical cover has fewer than three vertices, the actual degree is at
most two and Section 6 directly applies. There is no need to assume the
existence of extra physical vertices or to normalize as a cubic.

## 2. The elementary exterior deletion inequality

For each fixed feasible cubic support, choose any witnessing matching and its
unique edge incident to core `k`. That edge specifies a singleton support in
`a_k`; its remaining two matching edges specify a support in `b_ij`. The two
support weights multiply to precisely the original cubic role monomial.

Because independent formal role variables distinguish ordered endpoint supports,
different cubic supports cannot be mapped to the same resulting product
monomial. A product monomial from a cubic support is physically squarefree;
products with a shared exterior vertex are additional terms, not replacements
for that monomial. Each cubic support therefore has coefficient at least one
in `a_k b_ij`. This proves coefficientwise

    a_k b_ij - c >= 0.

Several possible matchings or deletion choices can only increase the positive
coefficient. No matching count is substituted for a Boolean support count.

## 3. Internal witness multiplicities, including opposite arcs

Fix an unordered internal pair `{i,j}`, with remaining core vertex `k`.
Each term of `w_ij=h_ij a_k` is a physically disjoint internal arc together
with one cross arc. For a prescribed endpoint support and this fixed unordered
pair, its endpoint roles determine at most one directed orientation of the
internal arc, and the outside vertex and its role determine at most one cross
arc at `k`. Thus the coefficient of each such support in `w_ij` is either zero
or one. In particular,

    0 <= w_ij <= H

holds coefficientwise. Having both `i→j` and `j→i` available does not create a
duplicate within `w_ij`, because the two orientations use different role
variables and give different ordered endpoint supports.

For a support contributing to `H`, all four physical vertices are used, two as
tails and two as heads. Its lone exterior vertex must be paired with a core
vertex of the opposite role. There are exactly two such core vertices in its
role pattern, and hence at most two candidate matching witnesses. Once that
partner is chosen, the remaining two core vertices must form the internal
edge, whose direction is forced. A candidate may fail because an arc is absent,
but there cannot be a third one. The support is feasible, so at least one
candidate succeeds. Therefore its coefficient in `sum w_ij` is one or two:

    H <= sum w_ij <= 2H.

Only the upper inequality is needed. Every witness has the same role monomial
as the support, so this is a weighted coefficientwise statement, not merely an
unweighted count. Multiplication of the deletion inequality by `h_ij` and
summation now gives the claimed coefficientwise bound

    E c <= sum w_ij b_ij.

## 4. Scalar ordering and exact Newton-gap decomposition

After specializing to arbitrary nonnegative role activities, order the three
`b_ij` values as `x>=y>=z>=0`, carrying their corresponding `w` values with
them. The producer's linear slack identity is exact:

    H(x+y) - (x w_x+y w_y+z w_z)
      = (x-y)(H-w_x)
        + y(2H-w_x-w_y-w_z) + (y-z)w_z.

All three terms are nonnegative by Section 3. Ties cause no issue, and there is
no division by any activity or coefficient.

The approved boundary inequalities imply

    A c <= xy+xz+yz.

Combining the two bounds and expanding gives

    gamma_2² - 3 gamma_1 gamma_3
      >= (z+H-(x+y)/2)² + 3(x-y)²/4 >= 0.

The stronger exact decomposition in the producer's note also checks term by
term. Its three additional remainders telescope as follows:

- Boundary remainders total `3[(xy+xz+yz)-Ac]`
- Deletion remainders total `3[sum w_ij b_ij-Ec]`
- Linear slack contributes `3[H(x+y)-sum w_ij b_ij]`

Together with the two squares they equal the original gap exactly. Sorting is
performed only after numerical nonnegative specialization. This proves the
scalar Newton inequality; it does not assert that the entire Newton gap is
coefficientwise nonnegative in the original role variables.

## 5. Independent exact corroboration

`check_assembly.py` imports no producer code. It enumerates matching supports
by adjoining a directed arc only when neither physical endpoint is already
used, and deduplicates ordered endpoint masks. Its formal monomials retain all
`2|V|` role exponents independently.

The run in `independent_receipt.json` passed:

- All 4,096 loopless directed graphs on three core vertices and one exterior
  vertex. There were 39,424 support instances. Among the 10,752 mixed rank-two
  supports, 9,216 had one internal witness and 1,536 had two. No fixed unordered
  internal pair contributed more than one witness
- All 20 role patterns of a fixed cubic support on three core and three exterior
  vertices. Deleting role-incompatible arcs leaves 1,600 graph cases, and all
  three choices of removed core give 4,800 checked deletion inequalities.
  The coefficient gaps were 0, 1, or 2
- 10,080 exact integer activity evaluations on 840 arbitrary directed relations
  with zero through six exterior vertices, with each role activity independently
  in `{0,1,2,3,4}`. Actual degrees were 0 in 955 cases, 1 in 2,360 cases, 2 in
  3,279 cases, and 3 in 3,486 cases. The decomposition identities, witness
  inequalities, sorted bound, two-square lower bound, and actual-degree Newton
  conditions all held

The first two checks are complete bounded localizations of their elementary
support claims. The last is corroboration only and is not promoted to an
all-size argument. The written proof already establishes every new step for
an arbitrary finite exterior set.

## 6. First Newton inequality, active arcs, and degree drops

Let an arc be active exactly when its product `u_tail v_head` is positive.
Zero-product arcs can be discarded without changing any evaluated support
coefficient: a support has positive weight precisely when every endpoint role
it uses is positive, in which case any witnessing matching consists of active
arcs. Thus the actual surviving degree `d` equals the maximum cardinality of
an active physically disjoint matching.

In the compatibility graph on active directed arcs, adjacency means physical
endpoint disjointness. Its clique number is exactly `d`. Give each arc its
positive product weight. The total vertex weight is `gamma_1`; the edge-weight
sum `W_0` counts rank-two matching witnesses. Every positive rank-two endpoint
support has at least one such witness, each of exactly its support weight, so
`gamma_2<=W_0`.

The producer's merging proof of the weighted clique bound is valid: for two
nonadjacent positive vertices, the edge-weight sum is affine in the division
of their fixed combined mass, because there is no edge between them. Moving
all their mass to the one with the larger weighted neighbor sum cannot reduce
that sum and eliminates one positive vertex. Iterate to a clique of size
`q<=d`. With total mass `M=gamma_1`, Cauchy gives

    W_0 <= (M²-sum m_i²)/2 <= (d-1)M²/(2d).

The redistributed masses need not remain products of endpoint activities; this
step is an auxiliary weighted-graph inequality and imposes no new restriction
on the original activity model.

Consequently, for `d>=2`,

    (d-1) gamma_1² >= 2d gamma_2.

At degree three this is the required first cubic Newton inequality
`gamma_1²>=3 gamma_2`. At degree two it is the stronger actual-degree condition
`gamma_1²>=4 gamma_2`. Degrees zero and one impose no Newton inequality, and
submatchings of any positive maximum matching give strictly positive
coefficients in every degree from zero to `d`. There are no internal zeros.
All degree drops caused by zero activities are therefore covered directly,
without continuity or a fixed cubic normalization.

## 7. Scope and conclusion

The new theorem applies to every finite loopless directed relation with a
physical vertex cover of size at most three, for independent nonnegative role
activities and endpoint supports counted once. The stated application to a
two-tail/three-head role cover whose tail vertices lie among the three head
vertices is valid, because their physical union is such a cover.

The argument does not settle physical covers of size four or five, arbitrary
two-tail/three-head covers with a larger union, real-rootedness, signed-monomer
stability, or correlation inequalities after internal arcs are added. No
transitivity assumption is used at any point.
