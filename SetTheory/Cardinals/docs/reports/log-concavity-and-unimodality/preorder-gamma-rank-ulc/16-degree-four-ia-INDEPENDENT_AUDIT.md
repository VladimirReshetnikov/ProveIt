# Degree-four preorder support polynomials: independent audit

## Approved statements

Let Γ_T(z)=Σ_k γ_k(T)z^k, where γ_k(T) counts ordered pairs of disjoint k-element subsets (A,B) admitting a directed perfect matching from A to B in the preorder T. Each pair is counted once, irrespective of the number of matchings.

The following claims have a complete finite exact certificate:

1. Every preorder on at most ten elements whose actual gamma degree is four is rank-ultra-log-concave.
2. Let K have at most ten elements, let v be a singleton source or singleton sink, and suppose ν(K−v)=3. Adjoin M independent pendant neighbors to v, oriented away from a source or toward a sink. For every integer M≥1, the resulting degree-four preorder is rank-ultra-log-concave. Moreover, each of its three order-four Newton gap polynomials is nonnegative for every real M≥0.
3. Together with the previously established actual-degree-at-most-three theorem, these statements settle the canonical Gallai–Edmonds sectors a=0 and a=1 at actual degree four.

This does not settle the general sectors a=2, a=3, or a=4.

## 1. Exact enumeration coverage

A preorder is a poset of equivalence classes with a positive size assigned to each class. Thus it suffices to cover all quotient posets and all positive assignments of block sizes summing to ten.

The quotient generator starts with the empty poset. To extend a poset Q by a new maximal vertex w, it tries every subset I of Q and accepts precisely the order ideals: there must be no comparison x<y with x outside I and y inside I. It then adds exactly the comparisons x<w for x in I. These are all and only the extensions having w maximal. Every nonempty finite poset has a maximal vertex, so induction proves coverage at every quotient size. The induction does not require naturally ordered labels.

The canonicalizer cannot merge nonisomorphic posets. Its key is the complete strict adjacency matrix after a permutation, encoded without collision in at most 100 bits of a 128-bit unsigned integer. Equal keys at a fixed quotient size therefore exhibit an isomorphism. Decoding the key retains an isomorphic representative, to which the same extension induction applies. Even failure of canonical invariance could only retain extra isomorphic representatives, not omit a poset.

In fact the canonicalizer is invariant. Its directed color refinement starts uniformly, includes the old color in every new signature, and orders signature classes lexicographically. Hence the partition only refines, and its labels are isomorphism-invariant. An unchanged number of colors means the partition is stable. The subsequent search considers every permutation inside each color class, except for permutations of vertices with exactly equal outgoing rows and incoming columns. Such vertices are incomparable and their transpositions preserve the entire relation, so the omitted permutations give identical matrices. Enumerating all multiset permutations of these row-column twin classes is consequently exact. The implementation’s name “true twins” should be read as “identical row-column twins”; the vertices are not adjacent true twins in the usual graph terminology.

For each m-vertex quotient, the recursive composition routine assigns all positive ordered m-tuples with sum ten. Every class-size assignment to every chosen quotient representative is included. There is no automorphism-based pruning of these assignments. Repetitions of isomorphic weighted quotients are harmless. The total number of weighted cases is therefore

Σ_(m=1)^10 p_m binom(9,m−1)=5,049,656,

where the independently reproduced quotient counts are

1, 2, 5, 16, 63, 318, 2,045, 16,999, 183,231, 2,567,284.

These familiar counts are consistency checks; coverage follows from the induction and collision argument, not from matching a known count.

Padding a smaller preorder by isolated singleton classes preserves every gamma coefficient, its matching number, and any marked vertex’s source/sink condition and deletion matching number. Thus enumeration at total size ten includes all required cases of size at most ten.

## 2. Degree and support counting

Let G(T) be the undirected simple graph joining distinct comparable elements. A feasible support supplies an ordinary matching of the same size. Conversely, each ordinary matching can be oriented edge by edge in an available preorder direction, giving disjoint source and target endpoint sets. Therefore deg Γ_T=ν(G(T)). Removing matching edges also proves γ_k>0 for every 0≤k≤deg Γ_T.

At ten vertices, ν=4 holds exactly when the graph has no perfect matching but has an eight-vertex induced subgraph with a perfect matching. The production degree filter tests exactly these conditions. Its perfect-matching recursion chooses the least remaining vertex and tries every possible partner, so it is exhaustive.

The support list contains each ordered disjoint equal-size pair once for sizes one through four. Its size is

Σ_(k=1)^4 binom(10,k)binom(10−k,k)=90+1260+4200+3150=8700.

For a listed pair (A,B), the production recursion selects the least element of A, tries every permitted target in B, and deletes that source and target. It returns a Boolean, not the number of successful branches. Induction on |A| proves that it counts support pairs and not matching multiplicities.

The separate Hall recount generates the same candidate domain through ternary vertex roles and tests every nonempty S⊆A for |N(S)∩B|≥|S|. It also uses a separate maximum-cardinality matching dynamic program and constructs block sizes from separator subsets. Only the audited canonicalizer is reused. Thus this independently reconstructs gamma and all marked deletion polynomials on the full enumerated domain.

All finite degree-four cases satisfy

3γ₁²−8γ₂≥0,   4γ₂²−9γ₁γ₃≥0,   3γ₃²−8γ₂γ₄≥0.

There are 686,481 such weighted cases, and the minimum of each gap is zero. Four disjoint two-element chains already attain equality, with Γ=(1+z)^4 on eight vertices; four disjoint two-element equivalence classes give Γ=(1+2z)^4. Degree four requires at least eight vertices. Consequently any degree-four counterexample must have at least eleven vertices.

## 3. Pendant certificate and endpoint specializations

A singleton source has no incoming off-diagonal arc, and a singleton sink has no outgoing off-diagonal arc. These are exactly the vertices selected by the implementation. A vertex in a nontrivial equivalence block cannot pass either test. An isolated vertex passes both but need only be counted once: the two orientations of its new star have the same support polynomial.

The deletion filter uses exact graph matching numbers and retains exactly ν(K−v)=3. Counting supports avoiding v then gives b_k=γ_k(K−v), independently of any matching witness. In particular b₃>0 and b₄=0. Since deletion of one vertex lowers matching number by at most one, K has degree three or four; there is no omitted higher coefficient.

Every support in the pendant expansion either avoids the new leaves or uses exactly one of them. In the latter case its partner is forced to be v. Removing that forced pair leaves precisely a support in K−v; conversely any such support and any one of the M leaves give an expanded support. Consequently

γ_k(K_M)=a_k+M b_(k−1),

where a_k=γ_k(K). This argument takes place at support level, so multiple matching witnesses introduce no multiplicity. The expansion is a preorder because extremality rules out any additional transitive relations involving a new leaf.

For M≥1 its matching number is exactly four: a three-edge matching in K−v plus one new pendant edge attains four, while any matching loses at most one edge on deleting v and all remaining leaves are isolated. At M=0 the core may have degree three, in which case the already proved degree-three theorem supplies its actual-degree normalization. The order-four interpolated inequalities remain certified at M=0 as well.

Each order-four gap is a quadratic q(M)=C+BM+AM². Nonnegativity on M≥0 follows from

A≥0, C≥0, and either B≥0 or 4AC−B²≥0.

Indeed B≥0 makes all terms nonnegative. If B<0, the discriminant condition forces A>0, and completing the square proves nonnegativity on the entire real line.

The complete marked-core computation covers 1,231,416 admissible marked weighted cases, producing 412,622 distinct pairs (a,b). Of these pairs, 393,218 have core degree four and 19,404 have core degree three. Independent verification reconstructs every quadratic by finite differences of its values at M=0,1,2, with primitive Newton factors derived from binomial coefficients. It checks all 1,237,866 quadratic instances. Of these, 180,706 have B<0, and their minimum 4AC−B² is zero. No inequality fails.

The phrase “1,237,866 distinct quadratics” in the original report should be replaced by “1,237,866 quadratic instances.” There are 670,629 different indexed quadratics after removing repeated triples (k,C,B,A). This wording correction has no effect on the mathematical certificate.

## 4. The complete a=0 and a=1 deductions

Apply the Gallai–Edmonds decomposition to G(T): D consists of vertices omitted by some maximum matching, A=N(D)\D, and C is the remainder. Write a=|A|, |C|=2c, and the nonsingleton components of D as having sizes 2d_i+1. The structure theorem gives

r=a+c+Σ_i d_i.

After removing the singleton D components as the exterior, the retained core K has

|K|=a+2c+Σ_i(2d_i+1)≤3r−2a,

and ν(K−A)=r−a. Every exterior vertex has neighbors only in A. This is the already established general bounded-core normal form, also obtained directly from the standard Gallai–Edmonds theorem.

For r=4 and a=0, C has total size at most eight and each nonsingleton D component has size at most nine. All nontrivial connected components are consequently within the finite bound. Each component is rank-ULC, using the degree-four finite theorem if its degree is four and the established lower-degree theorem otherwise. Supports split uniquely over components, so gamma polynomials multiply and actual degrees add. The finite-order ULC convolution theorem then proves rank-ULC for their product. The applicable primary statement is Gurvits, Theorem 1.1: ULC(l)*ULC(d) is ULC(l+d), https://arxiv.org/pdf/0804.1181.

For r=4 and a=1, write A={v}. The core has at most ten vertices and ν(K−v)=3. Every nonisolated exterior vertex is a pendant neighbor of v. If v→x for such a leaf x, an incoming arc u→v would force u→x by transitivity, contradicting the leaf’s unique neighbor; thus v is a singleton source. The reverse orientation makes it a singleton sink. Different leaves cannot have opposite orientations, since that would compare them by transitivity. The entire sector with nonempty nonisolated exterior therefore lies in the certified pendant family. If there are no nonisolated exterior vertices, the finite core certificate applies directly.

The standard graph-theoretic input is also stated in Douglas B. West, Theorem 5, https://dwest.web.illinois.edu/pubs/galledm.pdf. No degree-four real-rootedness assumption is used.

## 5. Reproducibility and reliability

The original finite scan has been recompiled with undefined-behavior sanitization and fully rerun, reproducing its log exactly. No arithmetic or runtime sanitizer finding occurred. The original source uses 128-bit integers for the pendant discriminant products; its other quantities are safely below signed 64-bit limits. In particular the ten-vertex support bounds are γ₁≤90, γ₂≤1260, γ₃≤4200, γ₄≤3150, and even the finite scan’s largest ratio cross-products are below 2×10^15.

The independent Python checker uses unbounded integer arithmetic, verifies uniqueness and ordering of all coefficient-pair rows, and compares all 35 archived files byte-for-byte with their expanded counterparts. The pair certificate SHA-256 is

df77d28bea6cc8cbf762925b07535bd117677d0206aaf72525efc7e96bcaed55.

The archive SHA-256 is

29dd251abc82d13edc6f0536ff359255757ad093b7b4bb900318c00b4adb6353.

Artifacts accompanying this note are audit_certificate.py, certificate_audit.json, recount_hall.cpp, hall_recount.log, hall_pairs.csv, and exhaust10_regenerated.log. This is a reproducible computer-assisted proof with explicit coverage arguments, not a proof-assistant formalization.
