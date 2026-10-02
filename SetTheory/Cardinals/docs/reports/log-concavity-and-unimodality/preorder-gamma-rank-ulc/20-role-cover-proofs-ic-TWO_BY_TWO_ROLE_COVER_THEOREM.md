# A two-by-two role-cover criterion for real-rooted support polynomials

Status: independently approved on October 1, 2026, including overlapping physical cover sets, smaller covers, and the exact weighted support bijection. No priority claim.

## Theorem

Let D be a finite loopless directed relation on V. Form its bipartite role graph with tail copies v_T, head copies v_H, and an edge i_T→j_H for every arc i→j of D. Suppose this bipartite graph has a vertex cover containing at most two tail copies and at most two head copies. Then for arbitrary nonnegative independent tail/head activities, D's signed physical monomer polynomial is real stable. Its support polynomial therefore has only negative real roots and is rank-ULC at its actual surviving degree.

The tail and head cover sets may represent overlapping physical vertices. Equivalently, there are subsets P,Q⊆V with |P|,|Q|≤2 such that every arc i→j satisfies i∈P or j∈Q. There is no transitivity assumption.

## Proof

Temporarily treat all tail and head copies as different physical vertices. Take the chosen tail-cover copies as the P core and the head-cover copies as the Q core. They are disjoint even when their original physical vertices overlap. The possible core arcs form an arbitrary subset of P×Q. All other vertices are exterior. Since the chosen copies form a vertex cover, no arc joins two exterior vertices. Every exterior tail points only to Q, and every exterior head receives arcs only from P. Thus the split relation is an instance of the independently approved arbitrary-subset-of-K2,2 family.

If either core side has fewer than two vertices, add isolated auxiliary core vertices to pad it. This only multiplies the monomer polynomial by their variables. The padded theorem gives stability; removing those isolated-variable factors preserves nonvanishing in the upper half-plane and hence stability of the original split relation.

Give tail copy v_T activity u_v and head copy v_H activity v_v. Activities in their unused opposite roles are irrelevant. The balanced-core theorem gives real stability of the split signed monomer polynomial with these weights.

For each original vertex v, merge its two monomer variables a=z_(v_T), b=z_(v_H) by the linear operator

    ab↦z_v, a↦1, b↦1, 1↦0.

Its algebraic symbol is z_v+r+s, which is stable. The finite-degree Borcea–Brändén theorem therefore preserves stability (or gives zero); the empty-support monomial with coefficient1 excludes the zero case. The pairs being merged are disjoint, so the process can be iterated over every vertex, including core/core and core/exterior pairs.

There is an exact support bijection. An original ordered disjoint support (S,T) has the unique split support consisting of the tail copies of S and head copies of T. Matching feasibility is identical because the arc relation is unchanged. Conversely, a split support survives all merges exactly when it uses at most one role copy of each original vertex, and then gives an original ordered disjoint support. Its weight is unchanged. Two distinct original role assignments may produce the same monomer but are distinct supports and are correctly added; this is not a matching-witness multiplicity. Thus the merged polynomial is exactly D's signed physical monomer polynomial.

The theorem for zero activities follows either directly from the already approved weighted split theorem or by coefficientwise continuity, with the empty-support monomial still present. The diagonal identity μ(t,...,t)=t^|V| Γ(−t^(−2)) gives negative real roots of gamma, and Newton's inequalities apply at the actual surviving degree.

## Core-internal-arc consequence

For disjoint physical P,Q with two vertices each and independent exterior I, the criterion allows arbitrary arcs inside P, arbitrary arcs inside Q, arbitrary P→Q core arcs, and arbitrary exterior attachments P→I and I→Q. Every arc has tail in P or head in Q. In particular, either direction or both directions inside either two-vertex side are permitted. It does not allow arbitrary Q→P or exterior/exterior arcs.

Concretely, a P-core vertex's head role is represented by an added pure exterior head copy; a Q-core vertex's tail role by an added pure exterior tail copy. The stable merge of that extra copy with its core counterpart is the only additional operation needed. This observation was supplied independently by the weighted-preorder researcher and avoids activity-ratio normalizations.

## Dependencies

- DISJOINT_CORE_EDGES_REAL_ROOTEDNESS.md: independently approved arbitrary-subset-of-K2,2 monomer theorem; final source hash1f0d2a69ec0ff8f7c1d0a5267afc30b76761c8a940a06f6cfecb5d3c9652343b.
- ../BALANCED_REAL_ROOTEDNESS_PROOF.md: physical-copy merge, arbitrary nonnegative role activities and actual-degree root transfer, independently approved.
- J. Borcea and P. Brändén, *The Lee–Yang and Pólya–Schur Programs. I*, Theorem1.1: https://arxiv.org/abs/0809.0401 .
