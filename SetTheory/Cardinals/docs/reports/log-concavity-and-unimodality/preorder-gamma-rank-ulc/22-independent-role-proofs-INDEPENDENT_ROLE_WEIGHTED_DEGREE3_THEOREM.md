# Independent-role-weighted preorder support polynomials: actual degree at most three

Status: complete proof synthesis submitted for independent global review. The final finite target has an independently approved exact all-real Rayleigh certificate; the final integrated ledger and this assembly are being checked. No publication or priority claim is made.

## Theorem and precise conventions

Let R be a finite preorder. Use only its off-diagonal arcs. Give each vertex i independent nonnegative tail and head activities u_i and v_i. Put

    gamma_k(R;u,v) = sum_(S,T) product_(i in S) u_i product_(j in T) v_j,
    Gamma_R(z;u,v) = sum_k gamma_k(R;u,v) z^k,

where the sum is over ordered disjoint k-element sets S,T for which a bijection S to T uses arcs of R. Each ordered support pair is counted once, regardless of the number of matching witnesses. Distinct ordered pairs with the same physical union remain distinct summands. In particular gamma_0=1.

If the actual surviving degree d of Gamma_R is at most three, then its coefficients are rank-ultra-log-concave:

    (gamma_k / binom(d,k))^2 >=
       (gamma_(k-1) / binom(d,k-1)) (gamma_(k+1) / binom(d,k+1)).

Equivalently, the only nonvacuous cases are

    d=2: gamma_1^2 >= 4 gamma_2;
    d=3: gamma_1^2 >= 3 gamma_2,
         gamma_2^2 >= 3 gamma_1 gamma_3.

No inequality is obtained by padding a degree-two polynomial to degree three. The result makes no general real-rootedness assertion; some degree-three preorder support polynomials have nonreal zeros.

The vertex-activity theorem is the specialization u_i=v_i=x_i. The present theorem strictly enlarges its activity scope; the earlier frozen vertex theorem and its proof package remain valid.

## 1. Reduction of zero activities to a positive-activity preorder

Let U={i:u_i>0} and V={j:v_j>0}. Retain an off-diagonal arc i->j precisely when it is an arc of R with i in U and j in V, and add every reflexive loop. Call the resulting relation R+.

R+ is a preorder. Indeed, a nontrivial two-step path i->j->k in R+ has i in U, k in V and i R k by transitivity of R. If i differs from k, the arc i->k survives; if i=k the needed loop was added. Steps involving a loop cause no difficulty.

Replace each zero role activity by one in its now-unused role. A positive-weight support of the original relation can use only surviving arcs, and every support of R+ uses only previously positive roles. Thus Gamma_R with the original activities equals Gamma_(R+) with the modified strictly positive activities. Unused zero roles cannot introduce a new support, because all arcs using them were removed. Therefore it suffices to prove the theorem with positive activities and underlying physical matching number at most three.

For positive activities, actual degree equals the matching number of the undirected comparability graph: orient each edge of a physical matching along any available preorder arc, while every support admits such a physical matching. This also shows that the filtered graph's matching number is exactly the original polynomial's surviving degree.

## 2. Universal first Newton gap

For d>=2, take the graph whose vertices are directed arcs and whose edges join physically disjoint arcs. Give arc i->j weight u_i v_j. Its clique number is d. Weighted Motzkin--Straus gives

    gamma_1^2 >= (2d/(d-1)) P_2 >= (2d/(d-1)) gamma_2,

where P_2 is the sum of products over unordered compatible arc pairs. Each size-two support is represented at least once in P_2 with its correct role weight; multiple matching witnesses only increase P_2. This settles all degrees at most two and the first cubic gap. Only the second cubic gap remains.

## 3. Exhaustive role-weighted finite theorem through seven vertices

All preorders on at most six vertices are covered by the approved role-weighted finite theorem SIX_VERTEX_ROLE_ULC.md and its independent exact audit. Total seven-vertex preorders are covered by the approved total-preorder role-weighted theorem.

The disconnected case needs no general convolution theorem. If one component has matching rank three, all others are isolated and the nontrivial component has at most six vertices. Otherwise every component has rank at most two; Section 2 makes each component polynomial real-rooted, and the product remains real-rooted.

For a connected bipartite preorder on seven vertices, a directed path through three distinct vertices would create a triangle. A nontrivial equivalence pair in a connected component with another vertex would also create a triangle by transitivity. Thus it is a height-two poset. Its directed role graph has matching number three and the approved role-matching-rank-three corollary applies.

It remains to cover every connected, nonbipartite, nontotal seven-vertex preorder of matching rank three. Exhaustive generation by naturally labeled quotient posets and positive equivalence-block compositions gives 131,645 redundant configurations, of which 75,160 are relevant; exact isomorphism and global duality reduce these to the 1,686 representatives in nontotal7_templates.json. The independent domain audit regenerates this catalog rather than assuming its completeness.

The complete independent-role ledger is nontotal7_hybrid_manifest.json. Each source is discharged by an approved structural theorem, an exact rational positive-orthant SOS certificate, an approved HPP side-matroid theorem, or an acyclic extremal-block refinement ending at a proved role-weighted target. No vertex-only certificate appears in this ledger. Relational refinement decreases the number of equivalent pairs, and every dependency chain has an explicitly proved terminal.

The last structural inputs are:

- ONE_TAIL_HPP_ROLE_COVER.md: a one-tail role cover whose dummy-augmented side transversal matroid has HPP gives a stable physical monomer polynomial and a real-rooted support polynomial. Loop removal, true parallel classes, pendant insertion and physical-role merging are exact support-once operations.
- The Kummer--Sert small-matroid classification and explicitly audited side maps close 27 sources. Six further side matroids are matched by exact basis isomorphisms to the published certified-positive nine-element HPP list. Those literature dependencies are explicit; the authors' original numerical searches are not used as local proof data.
- SIDE1565_HPP_FINAL_CASE.md closes target 1565. All twenty proper minors of its ten-element rank-five side matroid are HPP. Its Rayleigh difference at elements 0 and 9 has a rational 37-by-37 positive-semidefinite Gram matrix of rank 32, with a locally and independently replayed 32-square identity valid on all real assignments. Wagner--Wei, Theorem 3(c), gives side HPP. The one-tail theorem then gives real-rootedness under every independent role assignment. The existing extremal-block map closes source 1611.

Consequently the entire finite domain satisfies the second cubic gap for arbitrary positive or nonnegative independent role activities, always at the actual surviving degree.

## 4. Global Gallai--Edmonds assembly

Apply the approved graph-theoretic reduction in ../preorder-gamma-degree3/GALLAI_EDMONDS_REDUCTION.md and its structural audit. Let the physical matching number be three, let A be the canonical attachment set, and put a=|A|<=3. Remove all singleton components of D as an independent exterior X. The retained core K has at most 9-2a vertices. Exterior vertices are adjacent only to A.

Equivalent preorder vertices are adjacent true twins, so swapping them preserves the canonical D,A,C sets. Therefore an exterior singleton D component is a singleton equivalence class. All exterior neighbors of a fixed attachment have the same orientation: opposite orientations would force two exterior vertices to be comparable, or make a singleton exterior vertex equivalent to that attachment, contradicting the canonical structure. Hence the audited oriented templates apply.

### a=0

Each nontrivial connected component is either factor-critical on at most 2d+1<=7 vertices or perfectly matched on at most 2d<=6 vertices. Apply the finite theorem. Products at total rank at most three are handled exactly as in Section 3.

### a=1

The exterior consists of equally oriented pendant twins at the single attachment h. A support uses at most one such leaf, so sum their relevant tail activities (for source leaves) or head activities (for sink leaves) into one new pendant. Its unused opposite-role activity may be any positive number. This preserves the full independent-role support polynomial and the preorder structure.

If |K|<=6, the compressed preorder has at most seven vertices, covered by Section 3. If |K|=7, the GE budget forces K-h to consist of two rank-one factor-critical components of size three; exterior vertices become isolated when h is deleted. The independently approved all-rank articulation theorem gives real-rootedness for arbitrary independent role weights. If X is empty, the seven-vertex finite theorem applies directly.

The articulation theorem uses the exact decomposition

    Gamma = product_i (1+a_i z) [1 + sum_i (c_i z+d_i z^2)/(1+a_i z)],
    0 <= d_i <= a_i c_i,

when every component after deleting h has matching rank at most one. The inequality is support-level counting, and the resulting rational function is a nonnegative combination of upper-half-plane maps z/(1+a_i z) plus a real constant and a nonnegative multiple of z. This is the approved all-rank argument, not a general deletion-interlacing assumption.

### a=2

Here |K|<=5. The complete canonical family has 1,084 oriented core templates. All 494 mixed-sign templates are proved by exact heterogeneous-population compression, followed by 56 audited role-weighted finite certificates. All 590 same-sign templates are proved by 333 private-type reductions and 257 exact moment-cone certificates.

For a mixed shared exterior cloud, its sufficient statistics are H=sum v_x, T=sum u_x and W=sum u_x v_x, with 0<=W<=HT. The support polynomial depends only on these moments; the approved two-vertex compression realizes them using nonnegative effective activities. For same-sign shared clouds, U=sum w_x and E=sum_(x<y)w_x w_y satisfy 0<=E<=U^2/2. The full cone is parametrized by U=xi+eta, E=2 xi eta with xi,eta>=0. These proofs allow arbitrary finite populations and heterogeneous independent activities. Every finite certificate used by a compression has full role scope.

The exact formulas, catalog coverage and certificates are the independently approved A2_ALL_ROLE_ULC.md, A2_MIXED_ROLE_ULC.md and A2_SAME_SIGN_MOMENT_CONE.md inputs.

### a=3

The core is A itself. Every attachment is active toward the exterior. Choose its tail role if it points outward, or its head role if it points inward. These three roles cover all arcs. Exterior-to-core and core-to-exterior arcs are covered by construction. Any uncovered core arc would have an inward attachment i as tail and an outward attachment j as head. Choose exterior x with x->i and exterior y with j->y. If x differs from y, transitivity forces x->y, contradicting independence of the exterior. If x=y, the directed cycle makes that singleton exterior vertex equivalent to a core vertex, contradicting the canonical GE sets. Such a backward arc cannot occur.

The bipartite role graph therefore has matching number at most three. The approved role-rank-three corollary gives rank-ULC: by Konig, a mixed cover uses at most two roles on each shore and the approved two-by-two role-cover monomer theorem gives real-rootedness; a pure cover uses at most three tails or heads and the approved three-core Rayleigh theorem gives the required last gap. The latter proof allows all internal core arcs and arbitrary nonnegative independent role weights. The audited 17-template decomposition is an alternative supplementary verification.

These four cases exhaust matching rank three and finish the positive-activity theorem. Section 1 supplies all nonnegative activities and every original preorder whose surviving weighted degree is at most three, even when its unfiltered graph has larger matching number.

## 5. Verification and boundary

The final integrated ledger must be independently replayed with all receipt pins, every exact certificate, all structural maps and all refinement terminals. This note is the ordinary global assembly of those inputs; it does not replace their machine-checkable data. The released vertex packages are not modified.

The theorem is rank-ULC, not a general real-rootedness theorem. No higher-degree weighted assertion, no arbitrary-directed-relation degree-three theorem, and no unproved stability-preservation closure is inferred. Several structural subfamilies used here do enjoy real-rootedness, but the global conclusion is only the stated Newton inequalities.
