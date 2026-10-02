# Weighted five-vertex deletion interlacing and cut-vertex gluing

Status: all 96 marked five-vertex identities have passed a freshly implemented local exact checker. External review is pending. The finite proof is for preorders, not arbitrary directed relations.

## 1. The local interlacing lemma

Let H be a preorder on five vertices whose undirected comparability graph is factor-critical: deleting any vertex leaves a perfect matching. Mark a vertex h and assign positive independent tail/head activities. Write

Q(z)=Gamma_(H-h)(z)=1+a z+b z^2,
P(z)=Gamma_H(z)-Q(z)=c z+d z^2.

The exact finite lemma is

acd-bc^2-d^2 >= 0.                          (1)

The coefficients a,b,c,d are nonnegative. Under positive activities in the factor-critical case, b,c,d are positive. Since H-h has matching rank two, the universal weighted first-gap theorem gives a^2>=4b, so Q has two negative real roots. Inequality (1) says

Q(-c/d)=(d^2-acd+bc^2)/d^2<=0.

Thus the linear kernel L(z)=c+d z has its root between the two roots of Q. Equivalently, L/Q has nonnegative residues at the negative poles of Q. Double-root cases are obtained by limits, with cancellation where necessary. Therefore P/Q=z L/Q has nonnegative imaginary part in the upper half-plane.

This is the deletion-interlacing property needed for gluing. It is stronger than the rank-ULC conclusion for H itself, and is not being inferred from rank-ULC alone.

## 2. Complete finite certificate range

Every five-vertex preorder is obtained by expanding a naturally labeled quotient poset by positive equivalence-block sizes. There are 568 such redundant configurations. Exactly 98 have factor-critical comparability graphs. Marking every vertex and identifying marked isomorphisms and global order duality gives 96 marked types.

The canonical mark is vertex 0. An isomorphism carries activities with vertices; global duality exchanges tail and head activities. Both preserve (1). The catalog is `rank2_marked_five_templates.json`.

For each marked type, the polynomial acd-bc^2-d^2 is bihomogeneous of tail degree four and head degree four in ten independent role variables. The exact certificate files are `rank2_marked_five_certificates/t%03d.json`:

- 48 are coefficientwise nonnegative;
- 48 use small exact rational monomial-weighted square certificates;
- in total there are 258 square terms and 6,971 positive remainder monomials.

These are polynomial identities on the full nonnegative orthant. No numerical inequality or activity sample is used as a certificate.

Run `python verify_rank2_marked_five.py`. This standard-library checker imports no producer. It independently enumerates all forward quotient relations by bit masks and tests transitivity, reconstructs equivalence-block expansions, checks factor-criticality by the three perfect matchings on four vertices, regenerates marked isomorphism/duality coverage and multiplicities, compares Hall feasibility with explicit bijections on 4,896 candidates, and verifies all rational identities. Its receipt is `rank2_marked_five_verification.json`.

## 3. An all-rank gluing consequence

Let a preorder have a vertex h such that every component C_i after deleting h has the property that H_i=C_i union {h} is a factor-critical preorder on either three or five vertices. Any number of components is allowed. Then its role-weighted support polynomial is real-rooted.

Put Q_i=Gamma_(C_i), P_i=Gamma_(H_i)-Q_i. The exact support-level identity is

Gamma=product_i Q_i + sum_i P_i product_(j!=i) Q_j
     =(product_i Q_i)[1+sum_i P_i/Q_i].

Indeed, a support omitting h splits into component supports. A support using h has exactly one component containing an odd number of selected endpoints, namely the component matched to h. This determines the summand without selecting or counting a matching witness. Conversely, the component supports combine freely.

For a three-vertex factor-critical block, C_i is an edge and H_i has rank one. Hence Q_i=1+a_i z and P_i=c_i z, so P_i/Q_i=c_i z/(1+a_i z) maps the upper half-plane into its closure. For a five-vertex block, the lemma above gives the same conclusion from the positive-residue decomposition of (c_i+d_i z)/Q_i.

Thus 1+sum_i P_i/Q_i is either identically 1 or has strictly positive imaginary part in the upper half-plane. It cannot vanish there. The Q_i have only negative real zeros. By real conjugation, Gamma has only real zeros; nonnegative coefficients and constant term 1 make all its zeros negative. Zero activities follow by coefficientwise limits, and Newton's inequalities apply at the surviving degree.

## 4. Every seven-vertex factor-critical cut-vertex case

Let G be a factor-critical comparability graph on seven vertices and let h be a cut vertex. Since G-h has a perfect matching, every component C_i has even order. Their total order is six, and there is more than one component, so the only possibilities are 2+4 or 2+2+2.

Each H_i=C_i union {h} is factor-critical. Deleting h leaves the perfectly matched C_i. For v in C_i, a perfect matching of G-v must pair h inside C_i, because C_i-v has odd order and no other connections to the rest of G. Restricting that matching gives a perfect matching of H_i-v. Thus the local blocks have size three or five and satisfy the gluing theorem.

Consequently every role-weighted seven-vertex preorder with a factor-critical comparability graph and a cut vertex is real-rooted. This covers part of the GE a=0 finite domain. It does not settle the genuinely two-connected seven-vertex cases or the remaining a=1 cases.
