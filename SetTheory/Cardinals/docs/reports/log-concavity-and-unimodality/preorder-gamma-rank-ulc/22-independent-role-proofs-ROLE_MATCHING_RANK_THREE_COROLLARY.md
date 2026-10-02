# Role-matching rank at most three implies role-weighted rank-ULC

## Statement

Let R be any finite loopless directed relation. Its bipartite role graph has a tail copy v_T and a head copy v_H of every physical vertex v, with an edge i_T j_H for every arc i->j. Suppose the matching number of this bipartite graph is at most three.

Assign arbitrary nonnegative independent activities u_v for tail use and v_v for head use. Count each feasible ordered pair of disjoint physical endpoint supports once, with weight u_A v_B. Then the resulting gamma sequence is ultra-log-concave when normalized by its actual surviving degree.

This does not require transitivity. It is a corollary of the two independently approved structural theorems below and König's bipartite vertex-cover theorem; it is not a new proof of those inputs or a priority claim.

## Proof

By König's theorem the bipartite role graph has a vertex cover with at most three role vertices. Let P be its tail-side physical labels and Q its head-side physical labels. A physical label may belong to both sets, since the two role copies are distinct. Every arc i->j satisfies i in P or j in Q.

If both shores occur, then |P|<=2 and |Q|<=2. The independently approved two-tail/two-head role-cover theorem applies, including possible physical overlap of P and Q. It proves the stronger conclusion that the signed physical monomer polynomial is real stable and gamma has only negative real zeros. Newton's inequalities give rank-ULC at the actual degree.

If only one shore occurs, after duality there are at most three active tail vertices. Take them as the core C. Every other vertex has no outgoing arc, so the exterior is independent and all exterior arcs point from C to the exterior. Internal core arcs are arbitrary. The independently approved same-orientation three-core Rayleigh theorem therefore proves the desired rank-ULC assertion. If fewer than three active tails occur, the physical matching rank is at most two, and the universal weighted first-gap theorem also settles the claim directly.

A physical vertex-disjoint matching is a matching in the bipartite role graph, so the physical degree is at most three. The converse is false: a bipartite role matching may use one physical vertex once as a tail and once as a head. Zero activities may lower the surviving degree. In degree two the universal inequality is gamma_1^2>=4 gamma_2, not a padded cubic inequality; degree zero and one are vacuous. Thus every specialization has its own actual-degree normalization.

The same argument may be applied to the positive-arc role graph after deleting arcs whose product activity is zero.

## Approved dependencies

- `SAME_ORIENTATION_THREE_CORE_RAYLEIGH.md`, with independent approval in `../weighted-same-three-rayleigh-independent-audit/approval_receipt.json`.
- `../balanced-core-gamma-research/incomplete-core/TWO_BY_TWO_ROLE_COVER_THEOREM.md`, with independent approval in its `independent-audit/two_by_two_role_cover_audit_receipt.json`.
- The universal weighted first-gap theorem from arc-disjointness Motzkin–Straus.
- König's matching/vertex-cover theorem for finite bipartite graphs.

## Scope distinction

Role-matching rank and physical disjoint-support degree are different parameters. For example, a strict chain on four vertices has a role matching of size three but physical degree two. Conversely, a total equivalence class on seven vertices has physical degree three but role-matching number seven, so the hypothesis here does not cover all physical-degree-three preorders.

The general positive-role-weighted preorder theorem at physical degree three remains separate. Its unresolved portion in the current GE proof is the remaining finite seven-vertex factor-critical domain.
