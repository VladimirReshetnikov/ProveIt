# Independent audit of the degree-three Gallai–Edmonds reduction

## Verdict

The structural reduction in `GALLAI_EDMONDS_REDUCTION.md` is correct for every finite preorder, not only posets. Together with the existing small-core, one-attachment, and cover-three results, it gives the conditional theorem below. The only outstanding branch is two attachments; this audit does not assert that branch's inequalities.

The original article's Part IV support theorem and Part XII definitions use exactly the same unweighted ordered, disjoint tail/head support count as the certificates. In particular a bidirectional edge gives two degree-one supports, while multiple matching realizations of the same ordered endpoint pair give only one support.

## Degree and graph theorem

For the off-diagonal relation of a preorder, a support of size k has a realizing ordinary matching of size k in its simple undirected comparability graph. Conversely each ordinary matching can be oriented edge by edge along existing arcs. Distinct edges have disjoint endpoints, so the resulting tails and heads are disjoint. Thus degree equals matching number, even with equivalence blocks, and all coefficients through that degree are positive.

West's Theorem 5 gives the claimed canonical decomposition and the identity

    3 = |A| + |C|/2 + sum_i (|D_i|-1)/2.

Source inspected directly: Douglas B. West, A short proof of the Berge–Tutte Formula and the Gallai–Edmonds Structure Theorem, Theorem 5, printed pp. 3–4, https://dwest.web.illinois.edu/pubs/galledm.pdf. The near-perfect matchings internal to the D components count every component, including those receiving an A edge. Each A edge covers that component's otherwise-unmatched vertex. C is perfectly matched internally. Consequently there is no missing or double-counted term.

## Canonical exterior and transitivity

Let I consist of singleton D components and K be the complement. Then I is independent and N(I) is contained in A. Equivalent vertices are adjacent true twins, and their transposition is a graph automorphism. D is automorphism-invariant by its matching definition, as are A and C. An I vertex equivalent to any other vertex would therefore have an adjacent vertex in D, contradicting its singleton D component. This closes precisely the equivalence-block gap of an arbitrary chosen vertex cover.

All exterior incidences at a fixed attachment have one orientation: opposite orientations would give a directed two-step path between different independent exterior vertices. An exterior vertex can have a mixed direction profile across different attachments, but the sign assigned to each attachment is global. Its type is then its nonempty neighborhood subset of A; the signs already determine the directions.

Checking transitivity after adjoining one vertex of a type is sufficient for arbitrary populations of allowed types. A transitivity violation has a length-two witness. Witnesses with zero or one exterior vertex are already checked. A witness with two distinct exterior vertices must have the attachment as middle vertex, and would require both exterior orientations at that attachment. There are no exterior-to-exterior edges, so no remaining witness is possible. The same reasoning allows repeated vertices of a type and arbitrary nonnegative integer populations. There are at most 2^a−1 types.

## Core size and exhaustive branches

Write |C|=2c and |D_i|=2d_i+1 for nonsingleton D components. Each d_i>=1 and

    a+c+sum d_i=3,
    |K|=a+2c+sum(2d_i+1)<=9−2a.

Therefore a belongs to {0,1,2,3}; there are no unexamined cases.

- a=0: all nontrivial components have at most seven vertices, although their union may have nine. C has at most six vertices altogether, and each nontrivial D component has at most seven. Component support polynomials multiply: every realizing matching stays within components, forcing equal tail/head counts in each component; restrictions and unions give inverse support bijections. The finite <=7 real-rootedness result therefore settles this branch by multiplication and Newton's inequalities.
- a=1: all nonisolated exterior vertices are same-direction pendant twins. If any exist, the attachment is a singleton minimal or maximal vertex in the core; an incoming core arc in the outward case would force an unwanted second exterior neighbor, including if it came from an equivalent vertex. The support-level bijection is exactly Gamma_K+m z Gamma_(K−v), with no matching multiplicity. A pendant edge forces nu(K−v)<=2. If there are no nonisolated exterior vertices, the entire effective preorder has at most seven vertices and is already settled. Thus the one-attachment package covers this branch, including this otherwise-vacuous marked-vertex edge case.
- a=2: the core has at most five vertices; the possible exterior neighborhoods are {v1}, {v2}, {v1,v2}. At most two exterior vertices can occur in a support. Hence each coefficient has population degree at most two and the second cubic Newton gap has degree at most four. This is the sole remaining finite family of unbounded populations.
- a=3: the budget forces C empty and all D components singleton; hence K=A has precisely three vertices. The canonical exterior has no equivalence crossing. A three-edge matching uses exactly one core vertex per edge, so every attachment has an exterior neighbor. It is therefore included in the active-sign, 17-template enumeration, without exceptional bidirectional exterior types.

A useful additional bound for the a=2 worker: every graph built from a core of at most five vertices and an independent exterior adjacent only to two attachments automatically has matching number at most three. If a matching uses r exterior edges, then r<=2 and its size is at most r+floor((5-r)/2)<=3. No separate matching-rank filtering is needed for such templates.

## Exact linkage to the 17 templates

`cover3.py` exhausts the 29 labeled three-vertex preorders by enumerating all off-diagonal relations and testing transitivity. Each sign pattern and exterior neighborhood is subjected to the single-vertex transitivity test justified above. Its support kernel fixes selected exterior quotas, enumerates tail/head roles for each selected vertex and for the three core vertices, and tests existence of a bijection. Multiplying the resulting counts by products of binomial(population,quota) counts selected sets exactly once. At most three exterior vertices can be selected in a support, so its quota bound loses nothing.

Core permutations and global order reversal preserve all coefficients. Canonicalization therefore preserves the required inequalities. Regeneration in this audit checks the complete canonical key set, stored binomial gamma polynomials, stored gaps, and their monomial conversions against the export. The cube gap is computed as g2^2−3g1g3, not an ordinary matching-count gap.

## Normalization and conditional theorem

For actual degree three and g0=1, binomial normalization is exactly

    g1^2 >= 3g2,   g2^2 >= 3g1g3.

The article's first-rank inequality gives the first inequality for every directed relation: the arc-disjointness graph has clique number equal to the matching degree, and its edge count dominates g2. Thus all cover-three certificates need only establish the second gap. At degree two the correct first inequality is g1^2>=4g2; the same universal first-rank theorem gives it automatically. Positive coefficients through actual degree preclude internal zeros. A cubic ULC result alone must not be presented as cubic real-rootedness.

Conditional theorem: If the second gap g2^2−3g1g3 is nonnegative for every transitivity-compatible two-attachment family on cores of at most five vertices (with all three allowed exterior populations arbitrary nonnegative integers), then every finite preorder of actual gamma degree three is rank-ULC. Degrees zero and one are vacuous and degree two follows from the universal first inequality. The proof combines the four canonical branches above. It is enough to certify the larger two-attachment family; canonical neighborhood-surplus constraints need not be imposed.

## Presentation fixes

`GALLAI_EDMONDS_REDUCTION.md` still calls the one-attachment and 17-template inequalities unfinished. `COVER3_STATUS.md` is likewise an older partial status document. These status sentences should be updated, retaining the boundary condition of the 17-template result. Prefer the article's established unweighted rank-at-most-three bipartite theorem for cover class 0, rather than making the dependency appear to require a stronger weighted rank-four theorem.
