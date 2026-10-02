# Real stability with a two-edge balanced core

Status: independently approved, including final written-note review, on October 1, 2026. Audit receipt: independent-audit/star_core_audit_receipt.json. This note is separate from the frozen complete-core proof. No priority claim.

## Theorem and scope

Let P={p1,p2} and Q={q1,q2}. Let I be an independent exterior set, with arbitrary arcs P→I and I→Q. The only internal core arcs are p2→q1 and p2→q2. There are no other arcs. Isolated exterior vertices and absent attachments are permitted. For arbitrary nonnegative independent tail/head activities, the signed physical-vertex monomer polynomial is real stable. Consequently the directed support polynomial has only negative real roots and is rank-ULC at its actual surviving degree. Reversal and relabeling are included; no transitivity assumption is needed.

This includes canonical degree-four template6, core rows [0,0,0,3], orientation mask12: its active internal source is vertex3, its other source is vertex2, and its sinks are vertices0,1.

## Rank-two side polynomials

Split every exterior vertex into a head copy and a tail copy. On each side use the rank-two transversal matroid on its active copies and two private dummy elements. A private copy and the corresponding dummy form a parallel class; each common-neighbor copy forms its own parallel class. Isolated copies are excluded from the matroids but retained as monomer factors.

Let B_P and B_Q be their basis polynomials. Each is the elementary symmetric polynomial e2 in its parallel-class sums and therefore real stable. Let L_Q be the sum of all Q-side matroid variables. The coefficient

    A_P = ∂_{d_p2} B_P
        = d_p1 + sum of head-copy variables adjacent to p1

includes every common-neighbor head copy once, as well as copies private to p1. Here d_p2 is the dummy associated with the internally active source p2.

The split signed monomer kernel is

    H = B_P B_Q − A_P L_Q.

Indeed, the number of internal core edges is determined by an endpoint support: it is |S∩P| minus the number of selected exterior head copies. It is either zero or one, since both core arcs have the same tail. Zero core edges give B_P B_Q. With one core edge, p2 is its forced tail. The P-side residual is either the unused p1 dummy or one exterior head matched from p1, exactly A_P. On the Q side, the residual is either one unused core dummy or one active exterior tail copy, exactly L_Q. In the latter case the exterior tail may have two possible neighbors, but its endpoint support is counted once. The two arcs from p2 to Q ensure these side conditions are sufficient. No support is counted by its number of matching witnesses.

## Stability by an upper-half-plane shift

For Q-side parallel-class sums r1,...,rk, the polynomial

    B_Q + s L_Q = e2(r1,...,rk,s)

is real stable. Fix all Q-side variables in the open upper half-plane. Both B_Q and L_Q are nonzero: B_Q by stability, and L_Q because its imaginary part is strictly positive. The unique root in s is −B_Q/L_Q; stability implies that it is not in the open upper half-plane. Thus Im(B_Q/L_Q)≥0. Since the ratio is nonzero, Im(−L_Q/B_Q)≥0 as well.

The basis polynomial B_P is affine in its dummy d_p2. Therefore

    H = B_Q · B_P(d_p2 − L_Q/B_Q),

where all other P-side arguments are unchanged. The shifted dummy is still strictly in the upper half-plane, since d_p2 is strictly upper and −L_Q/B_Q is closed upper. Stability of B_P now makes this expression nonzero. Hence H is real stable. This argument uses no unproved closure under adding a positive polynomial.

## Signed monomers, activities, and physical merging

Give each core dummy its core monomer variable and substitute −1/z_x for each active exterior-copy variable. Let Z be the product of all exterior-copy monomer variables, including isolated copies. Then the split signed monomer polynomial is ZH after these substitutions. Multiaffinity cancels every denominator, and the negative reciprocal map preserves the upper half-plane, so this polynomial is real stable.

Positive activity w_i on each split vertex is introduced by the transformation μ(z)↦(∏w_i)μ(z_i/w_i). Give a tail copy the physical tail activity and a head copy its physical head activity; core source and sink vertices receive their relevant activities. This produces the correct product weight for each used endpoint.

For each physical exterior vertex merge its two monomer variables a,b by the linear map

    ab↦z, a↦1, b↦1, 1↦0.

Both unused copies become one unused vertex; either single-used role survives with its correct activity; simultaneous use is removed. This is exactly physical disjointness. Its plus-sign algebraic symbol is z+r+s, real stable. The Borcea–Brändén finite-degree stability-preserver theorem, with the usual stable factors for untouched variables, proves stability after each merge. The empty-support monomial has coefficient1, so no stage is the zero polynomial. Zero activities follow by continuity, again with this nonzero monomial surviving.

For N physical vertices the diagonal is μ(s,...,s)=s^N Γ(−s^(−2)). Real stability makes this a real-rooted univariate polynomial. Any nonzero root ρ of Γ that were not negative real would give a nonreal solution of s²=−1/ρ, impossible. Since Γ(0)=1, its roots are all negative real. Newton's inequalities apply at its actual degree, including degree loss at zero activities.

## Dependencies

- Rank-two e2 stability and the same weighted monomer/merge mechanism are detailed in ../BALANCED_REAL_ROOTEDNESS_PROOF.md, independently approved and frozen.
- J. Borcea and P. Brändén, *The Lee–Yang and Pólya–Schur Programs. I. Linear Operators Preserving Stability*, Inventiones Mathematicae177 (2009),541–569, Theorem1.1: https://arxiv.org/abs/0809.0401 .
- D. G. Wagner, *Multivariate stable polynomials: theory and applications*, Theorems3.1 and5.2 and Lemma2.4: https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf .
