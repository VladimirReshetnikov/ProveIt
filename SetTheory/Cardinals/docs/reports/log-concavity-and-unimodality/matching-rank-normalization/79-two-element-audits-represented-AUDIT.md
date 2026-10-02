# Audit of the fully multivariate selected-tail theorem

Verdict: approved for the stated representable-matroid scope. Final reviewed source FULL_SELECTED_TAIL_THEOREM.md, SHA-256 3d27a6f26c3877b2aec0e62ecd69eb3a9142337016e2dc1293ed4bbf0b5e70e1.

This review checks the new augmentation, contraction and low-rank induction independently of the producer's computational checks. The principal-line seed was part of the earlier independently approved two-tail work; the present reviewer contributed to that earlier theorem. The new fully multivariate argument does not assume a stronger result about physical collisions or arbitrary matroids.

## Augmented representation and Boolean support

The augmented matrix has rank q+n: the old ground set spans the q old rows and the new dummy columns span the n new rows. A basis omitting r dummy columns must obtain the r missing new-row directions from its selected distinguished columns; therefore r≤2. For r=0, its old part is an ordinary M basis with zero, one or two distinguished elements. For r=1, a single selected distinguished element leaves an old basis; two selected distinguished elements leave one residual extension. The private rows force which element remains, while the common row gives a linear combination of the two old minors with independent new indeterminates. It is nonzero exactly when either extension is feasible. For r=2, both distinguished elements must be selected; their new-row determinant is nonzero precisely for a matchable pair of head types and the old part must be a basis.

Thus the augmentation counts each basis once, not its row allocation witnesses. Distinct possible common-row allocations cannot cancel because their new indeterminates are independent. Numerical head activities are basis weights applied afterward, not substituted into those generic representation entries. The weighted basis specialization is exactly z^(n−2)F_M. Its nonzero z^n U0 term persists at zero population weights. The argument uses monomial translation only for M-convex support, not for Lorentzian coefficients.

## Contraction and induction

Differentiating an old nonloop variable selects old subsets containing that element and then removes it. This gives exactly the five polynomials U0,UA,UB,U,V for M/e; in particular the Boolean union remains a union, not a sum with duplicated intersection. If the old element is a loop the derivative is zero. The old remaining ground set spans the quotient, which is representable and has rank q−1. Distinguished elements becoming loops or parallel are allowed. This proves closure under every nonzero old-variable derivative.

Consequently any derivative of order q involving an old variable is controlled by induction. Among a,b,z derivatives, the separate exponent bounds1,1,2 leave only the listed ranks0–4 cases. No higher-rank cases are omitted.

## Low-rank checks

At rank zero the three-variable quadratic has exactly the stated Hessian and determinant2M2(R0R1−M2). The moment identity R0R1−M2=H²−S and a negative principal minor give at most one positive eigenvalue, including zero determinant. Common-head perturbations cover the M2=0 boundary.

At rank one, the polynomial before u is replaced by the old-variable sum is itself the construction for one old nonloop and the same distinguished loop indicators. This explicitly supplies M-convex support. All four indicator pairs were checked. The a/b derivative matrices, nonnegative determinant slacks and the z derivative's negative-semidefinite Schur block are correct, with no assumption of nonloop distinguished elements. Perturbation handles zero population moments.

At rank two, all four displayed identities agree exactly. Their seed substitutions are nonnegative linear maps. Since V is a nonnegative constant, each correction removes a nonnegative square in a single coordinate, hence subtracts a positive-semidefinite diagonal Hessian matrix. This cannot create a second positive eigenvalue. The actual derivatives retain their nonnegative coefficients. Perturbing with two common heads simultaneously makes M2,R0,R1 positive; the resulting polynomials converge to the original, so the denominator boundaries are harmless.

At rank three, the two z² derivatives are the stated special-variable derivatives of the Lorentzian seed. The remaining derivative is obtained by a nonnegative directional derivative and a nonnegative specialization because some coordinate of Jm is positive whenever m≠0. When m=0 it is2zV, with V a rank-one contraction basis polynomial or zero. At rank four,2V is a rank-two contraction basis polynomial or zero. All q≥5 derivatives involving only a,b,z vanish.

Together with the M-convex support already established, these signatures prove the fully multivariate theorem by the primary quadratic-derivative characterization.

## Graph specialization and scope

The transversal matroid with private Q dummies satisfies the old-spanning hypothesis. The stated substitutions retain all selected-left variables individually and introduce Q head activities by a positive linear scaling and an overall positive factor. The explicit endpoint formula cancels reciprocal dummy weights before taking zero-head limits; its empty-support monomial has coefficient one. Tail activities are independent nonnegative variable scalings.

The proof is ordinary and all-size. It establishes the representable-matroid theorem and its graph corollary exactly as stated. It does not yet remove representability, make Y activity parameters homogeneous variables, justify physical role-copy collisions, assert real stability or replace the unchanged released paper.

## Independent supplementary replay

The separate check.py imports no producer code. It verifies the q0 determinant, all four q1 indicator cases, eight rank2–4 derivative identities and the directional-derivative identity. On32 rationally represented matroids of ranks0–4, including loops and parallel distinguished elements, it checks250 literal symbolic augmented-basis identities (12,524 candidate bases) and1,240 old-element contraction identities, with zero population weights included. These finite checks corroborate the ordinary argument; they are not theorem premises or a rank bound. The checker rejects optimized Python and supports portable source/output arguments.
