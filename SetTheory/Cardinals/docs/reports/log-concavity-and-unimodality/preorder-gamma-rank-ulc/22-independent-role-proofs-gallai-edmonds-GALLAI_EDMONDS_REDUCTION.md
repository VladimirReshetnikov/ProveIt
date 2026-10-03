# Final branch-status update

All remaining positivity branches are now exact-certified: a=1 in one-attachment/README.md, a=2 in two-attachment/README.md, and a=3 in COVER3_CERTIFICATES.md. Their generators and algebraic identities have independent exact checks. The structural reduction below is unchanged; its earlier statements that positivity remains unfinished are historical and superseded by those reports. Taken together with the finite a=0 case and the universal first Newton inequality, these results establish rank-ULC for every finite preorder of actual gamma degree three, as an exact computer-assisted theorem.

# Checked Gallai–Edmonds reduction for actual gamma degree three

## Conclusion

The proposed reduction is valid. It reduces arbitrary finite preorders of actual gamma degree three to (i) a finite real-rooted component case, (ii) bounded cores with one pendant-twin population, (iii) bounded cores with at most three two-attachment exterior populations, and (iv) the existing 17 three-cover templates. This document establishes the reduction, NOT positivity in the still-uncertified families.

## Standard graph-theoretic input

For a finite simple graph G, define D as the vertices omitted by some maximum matching, A=N(D)\D, and C=V(G)\(A∪D). The Gallai–Edmonds structure theorem says that the components D_i of G[D] are factor-critical, G[C] has a perfect matching, and every maximum matching pairs all A vertices into distinct D_i, together with internal near-perfect matchings in the D_i and a perfect matching in C. Therefore

ν(G)=|A|+|C|/2+Σ_i (|D_i|−1)/2.

A primary proof source is Douglas B. West, *A short proof of the Berge–Tutte Formula and the Gallai–Edmonds Structure Theorem*, Theorem 5, pp.3–4: https://dwest.web.illinois.edu/pubs/galledm.pdf. The same standard theorem is Theorem 3.2.1 in Lovász–Plummer, *Matching Theory* (1986). None of this theorem is claimed new.

## Canonical exterior and the core-size bound

Apply the theorem to the undirected comparability graph of the preorder. Let I be the union of all singleton components of G[D], and let K=V(G)\I. Distinct I vertices are nonadjacent. Every neighbor of I lies in A: it cannot lie in another D component, and C has no D neighbors by definition.

Put a=|A|. Write |C|=2c, and for each nonsingleton D component write |D_i|=2d_i+1 with d_i≥1. Since ν(G)=3,

a+c+Σ_i d_i=3.

Consequently

|K|=a+2c+Σ_i(2d_i+1) ≤ a+3(c+Σ_i d_i)=9−2a.

The inequality uses 2d_i+1≤3d_i. In particular a≤3, with bounds7,5,3 when a=1,2,3. Isolated vertices in I have no effect on any gamma coefficient and may be discarded.

## Why exterior equivalence blocks cannot occur

If u and v are equivalent in the preorder, then for every third vertex w, both directed comparability relations to w agree, by transitivity. In particular u,v are adjacent true twins in G, and their transposition is a graph automorphism.

The set D is invariant under every automorphism because its definition uses only maximum matchings. So are A=N(D)\D and C. Thus equivalent vertices belong to the same one of D,A,C. If x is in a singleton D component and is equivalent to another vertex y, then y is also in D and adjacent to x, contradicting that its D component is singleton. Every x∈I is therefore a singleton preorder equivalence class.

This proves, for the canonical exterior, the hypothesis absent from an arbitrary three-vertex-cover construction. There are no bidirectional arcs between I and K.

For any fixed a∈A, all its arcs with exterior vertices point the same way: if x<a<y for distinct x,y∈I, transitivity makes x,y comparable, impossible. Since bidirectional arcs have been excluded, this argument applies even if a has only one exterior neighbor. A vertex with no exterior neighbors needs no orientation choice.

Hence an exterior type is determined by its nonempty neighborhood subset of A and the fixed orientation at each neighboring attachment vertex. There are at most 2^a−1 types, with arbitrary nonnegative integer populations subject to the unary transitivity-compatibility conditions from the core. Once these signs are fixed, independent allowed types cannot generate paths between distinct exterior vertices.

## Branch a=0

There are no attachments. The graph components lie wholly in C or are D components. C has at most6 vertices in total, and each nonsingleton D component has at most7 vertices. Isolated singleton D vertices are irrelevant.

Every nontrivial component thus induces a preorder on at most7 elements. The exact small-preorder enumeration in `small-check/` independently certifies real-rooted gamma for all preorders in that range, including the lower-degree cases. Gamma polynomials multiply over disjoint comparability components because every feasible support splits uniquely into component supports. A product of real-rooted polynomials is real-rooted. Thus this entire branch is settled by the finite lemma; one need not import a separate ULC convolution theorem.

## Branch a=1

Let A={v}. After discarding isolated exterior points, all m outside vertices are pendant twins adjacent only to v, with a common direction. The induced core preorder has at most7 vertices.

Every feasible support either avoids the exterior, or uses exactly one exterior point. In the latter case the matching must use its unique incident edge with v, and deleting those two endpoints leaves precisely a feasible support in K−v. This bijection is at support level and introduces no matching multiplicity. Therefore

Γ_G(z)=Γ_K(z)+m z Γ_(K−v)(z).

Transitivity imposes a useful additional restriction: if v→x, then v has no incoming off-diagonal arc from the core; otherwise u→v→x would force a second neighbor of x. Thus v is a singleton minimal element. For x→v, v is a singleton maximal element.

If m≥1 then ν(K−v)≤2, since one exterior edge could be added to any matching there. Thus the formula stays degree≤3 for every m≥0. Its two degree-three Newton gaps are quadratic polynomials in m. If m=0, the core is already covered by the finite≤7 computation.

## Branch a=2

The core has at most5 vertices. The nonempty exterior neighborhood types are {v₁}, {v₂}, and {v₁,v₂}, with each attachment’s orientation fixed. Some of those types may be forbidden by core transitivity. There are no split equivalence classes.

Every exterior vertex in a disjoint matching needs a distinct attachment vertex, so at most two exterior vertices occur in any support. Thus every gamma coefficient has population degree≤2; γ₁ has degree≤1. In particular the second Newton gap has degree≤4 in at most three population variables. This yields a finite low-dimensional exact positivity problem. It is not solved by this reduction alone.

## Branch a=3

The matching-budget identity forces C=∅ and every D_i singleton. Hence K=A has exactly three vertices, and the comparability graph has this three-vertex cover. The equivalence argument above guarantees no class crosses the boundary. This is exactly the setting of `cover3_seventeen_templates.json` and its checked generator: 17 templates under permutation of core vertices and reversal of all arcs.

No further types or singleton-capacity bidirectional exceptions are needed in this canonical branch. Actual Gallai–Edmonds partitions impose extra neighborhood-surplus conditions, but proving the 17 template inequalities on all nonnegative integer populations is stronger and avoids needing to enforce them.

## Remaining work and proof status

The reduction uses a standard published graph theorem and elementary arguments supplied above. It does not turn the unproved 17-template inequalities or the one-/two-attachment finite checks into established results. The finite≤7 lemma is an exact, reproducible computational theorem with an independent checker, not a proof-assistant formalization. The previously proved P⊕A_m⊕Q family is independent of the unfinished branches.
