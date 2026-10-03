# Vertex-weighted preorder gamma: actual degree at most three

Status: the complete local proof ledger and all exact residual certificates are ready. Independent audit of the vertex specialization, exhaustive residual-domain closure, and global GE reduction is in progress. No publication or priority claim is made.

## Theorem

Let R be a finite preorder and give every physical vertex a positive activity x_v. Define

gamma_k(R;x)=sum_(A,B) product_(v in A union B) x_v,

where the sum is over ordered pairs of disjoint k-element vertex sets A,B for which a bijection A->B uses off-diagonal preorder arcs. Each ordered support pair is counted once, regardless of how many matching witnesses realize it. Different ordered support pairs with the same union are still different summands.

If the actual degree d of Gamma_R(z;x)=sum_k gamma_k z^k is at most three, then gamma_k/binom(d,k) is log-concave. Equivalently:

- d=2: gamma_1^2>=4 gamma_2;
- d=3: gamma_1^2>=3 gamma_2 and gamma_2^2>=3 gamma_1 gamma_3.

Degrees zero and one are vacuous. The conclusion also holds for nonnegative vertex activities at their actual surviving degree: delete every zero-activity vertex, which preserves the weighted polynomial, and apply the positive-activity theorem to the induced preorder.

This is the single-vertex-activity theorem. It does not assert the still-unproved general independent-tail/head-activity theorem at physical degree three.

## 1. Universal first gap and actual degree

With positive activities, actual degree equals the matching number of the undirected comparability graph. Indeed, every physical matching can be oriented along preorder arcs and gives a feasible support, and every feasible support has a physical matching.

For d>=2, weighted Motzkin–Straus on the arc-disjointness graph gives

gamma_1^2 >= [2d/(d-1)] gamma_2.

The compatible-arc-pair sum may count a support more than once, so it is an upper bound for gamma_2, in the direction required by this inequality. This settles every degree-at-most-two case and the first cubic gap. Only gamma_2^2>=3 gamma_1 gamma_3 remains at actual degree three.

## 2. Complete finite theorem through seven vertices

All preorders on at most six vertices are already covered by the independently approved stronger role-weighted theorem in `SIX_VERTEX_ROLE_ULC.md`.

For seven vertices:

- Matching rank at most two is universal as above.
- A disconnected rank-three graph either has a rank-three component on at most six vertices and only rank-zero other components, or all nontrivial components have rank at most two. In the latter case their support polynomials are real-rooted by the first-gap theorem, and the product is real-rooted.
- A connected bipartite preorder on seven vertices is a height-two poset: a directed path through three distinct vertices would create a triangle, and a nontrivial equivalence pair in a larger connected component would also create a triangle. Its role graph has matching rank three. The approved role-matching-rank-three corollary applies (alternatively, the prior weighted bipartite rank-three theorem suffices).
- Total preorders are covered by the independently approved full role-weighted degree-three theorem.
- The remaining domain is every connected, nonbipartite, nontotal seven-vertex preorder of matching rank three.

The remaining domain is completely enumerated by naturally labeled quotient posets and positive equivalence-block compositions. The 131,645 redundant configurations contain 75,160 relevant configurations and reduce to 1,686 representatives under isomorphism and global duality. The exact catalog is `nontotal7_templates.json`.

`nontotal7_vertex_complete_manifest.json` is the separate complete vertex-weighted ledger for all 1,686 representatives. It combines independently approved structural role-weighted theorems, exact role certificates specialized by u_i=v_i=x_i, and direct seven-variable vertex certificates. The frozen underlying role ledger is `vertex_support_role_snapshot.json`; its incompleteness is not concealed or promoted to a role-weighted theorem.

There are 100 newly generated vertex certificate files in `nontotal7_vertex_certificates/`. All 100 pass the fresh Hall-based checker `verify_weighted_certificate_file.py`, with 5,342 square terms and 26,933 positive remainder monomials. Three are redundant in the current selected manifest because new stronger role certificates arrived meanwhile. Each identity is a rational sum of nonnegative monomial multiples of polynomial squares plus a polynomial with nonnegative coefficients. The receipt is `vertex_seven_certificate_verification.json`.

The specialization retains multiplicity of distinct ordered supports. It does not identify all supports having the same union. Global duality simply exchanges the ordered tail and head sets and therefore preserves the vertex-weighted polynomial.

### Refinement-scope safeguard

A role-weighted extremal-block reduction may create unequal tail/head activities, even when the original activities satisfy u=v. Consequently no vertex-only target theorem is used to justify a refinement. Every inherited refinement in the vertex ledger has a terminal proof entirely within the independent-role ledger. Every still-conditional role-refinement source is instead given its own direct vertex certificate unless a new full role certificate for that source has arrived. The builder checks these scope conditions explicitly.

## 3. Gallai–Edmonds reduction for arbitrary vertex count

Use the approved combinatorial reduction in `../preorder-gamma-degree3/GALLAI_EDMONDS_REDUCTION.md`, `STRUCTURAL_AUDIT.md`, and `THEOREM_SYNTHESIS.md`. Its graph-theoretic statements are unaffected by positive vertex activities.

For matching rank three, let A be the canonical GE attachment set and put a=|A|<=3. Remove the singleton components of D as an independent exterior. The retained core K has at most 9-2a vertices.

Equivalent preorder vertices are adjacent true twins, so their swaps preserve the canonical sets D,A,C. A singleton D component is therefore a singleton equivalence class. At each attachment all exterior neighbors have the same orientation; opposite directions would, by transitivity, make two exterior vertices comparable. Thus the exact weighted templates used below apply.

### a=0

Every nontrivial connected component has at most seven vertices: an odd factor-critical component has size at most 2d+1, while a perfectly matched component has size at most 2d. Apply the finite theorem. Since the total matching rank is at most three, products are handled by the disconnected argument in section2; no unproved general convolution closure is needed.

### a=1

The core has at most seven vertices and all exterior vertices are equally oriented pendant twins at the sole attachment h. Only one exterior vertex can occur in a support. Sum their relevant activities into one pendant activity S.

This compression preserves the single-vertex-weighted setting: for sink leaves, choose both new role activities equal to S, since the tail activity is unused; for source leaves the head activity is unused. Core activities remain x_v. If |K|<=6, the compressed preorder has at most seven vertices, so the finite vertex theorem applies.

If |K|=7, the GE rank budget forces K-h to consist of two nontrivial rank-one factor-critical components, each on three vertices; the exterior becomes isolated after deleting h. The approved all-rank articulation theorem applies directly under arbitrary role activities, hence also under vertex activities. If the exterior is empty, the seven-vertex finite theorem already applies.

### a=2

The core has at most five vertices. The entire two-attachment family is independently proved under arbitrary independent role activities and arbitrary heterogeneous exterior populations. See `A2_ALL_ROLE_ULC.md`, `A2_MIXED_ROLE_ULC.md`, and `A2_SAME_SIGN_MOMENT_CONE.md`. Specializing u=v gives the desired vertex result. No vertex-only target is used inside its potentially non-vertex-weight-preserving compression.

### a=3

The core is A itself. The approved mixed-three-core real-rootedness theorem covers the eight mixed-orientation classes. The approved rank-three Rayleigh argument covers all nine equal-orientation classes, including arbitrary internal core arcs. Together they cover every exterior population and activity assignment. See `MIXED_THREE_CORE_RR.md` and `SAME_ORIENTATION_THREE_CORE_RAYLEIGH.md`.

These four cases exhaust the GE reduction and prove the theorem for arbitrary vertex count at actual degree at most three.

## 4. Independent-audit boundary

The new work requiring final independent closure is the vertex-only specialization and its complete seven-vertex ledger, together with the short global argument above. The role-weighted structural inputs already have their own independent approval receipts, pinned by the manifests. The universal first-gap and the graph-only GE reduction are explicit earlier dependencies.

The larger role-weighted problem remains separately tracked in `nontotal7_hybrid_manifest.json`. Completing this vertex theorem must not change that ledger's unresolved role-weighted entries.
