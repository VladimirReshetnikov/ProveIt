# Ordinary first-layer Hessian inequality for any number of tails

Status: independently approved by root on October 1, 2026 at15:40 UTC; the producer independently reconstructed the core matrix argument at15:37 UTC. No claim of full Lorentzianity at arbitrary rank is made.

## The matrix inequality

Fix r≥2 left vertices and arbitrary neighborhoods in a finite weighted set of right vertices. Activities v_y are independent nonnegative constants. Let R_i be the total activity of neighbors of i, H_ij the total activity of common neighbors of i and j, and Q_ij the sum of squared activities of those common neighbors. Let R_ij sum v_y v_w over unordered distinct head pairs {y,w} admitting a matching to {i,j}, each feasible head pair counted once. The product R_iR_j counts the forbidden repeated-head choices with total weight Q_ij and counts each distinct common-head pair twice, with excess (H_ij²−Q_ij)/2. Hence

    R_ij = R_i R_j − (H_ij²+Q_ij)/2.                 (1)

The r-by-r symmetric matrix

    N_ii=(r−1)R_i²,
    N_ij=(r−1)R_iR_j−rR_ij  (i≠j)                  (2)

is positive semidefinite.

For positive R_i put p_i(y)=v_y/R_i on neighbors, and zero otherwise; let u_i=(sqrt(p_i(y)))_y. Define

    A_ij=(u_i·u_j)²,
    C_ii=1,     C_ij=sum_y p_i(y)p_j(y) (i≠j).

For arbitrary real x, the symmetric operator T=sum_i x_i u_i u_i^T acts on a space of dimension at most r, has trace sum_i x_i and squared Hilbert–Schmidt norm x^T A x. Therefore

    x^T A x ≥ (sum_i x_i)²/r.                       (3)

Independently sample one label from each p_i. The equality partition π has at most r blocks, and its matrix K_π satisfies

    x^T K_π x = sum_{B in π}(sum_{i in B}x_i)²
                  ≥ (sum_i x_i)²/r.

Since E K_π=C, this proves C≥J/r, where J is the all-ones matrix. Equation (3) similarly says A≥J/r. For D=diag(R_i), direct substitution in (1) gives

    D^(-1)ND^(-1)=(r/2)(A+C)−J
                  =(r/2)(A−J/r)+(r/2)(C−J/r) ≥0.   (4)

If R_i=0, the corresponding row and column of N vanish: every positive-weight eligible head is absent. Apply the argument to the remaining indices using the original denominator r, since their span dimension and number of partition blocks are still at most r. This includes all zero-weight and empty-neighborhood boundaries.

Both inequalities hold for arbitrary signed real test vectors. In particular the proof establishes positive semidefiniteness, not merely nonnegativity on the positive orthant. It uses two finite-dimensional Cauchy–Schwarz inequalities and exact support counting, with no computational premise.

## Exact derivative interpretation

Let R_S be the sum of product head activities over head subsets of size |S| that can match the left subset S, counted once. Define the homogeneous selected-tail polynomial

    F(z,a)=sum_{S⊆[r]} R_S (product_{i∈S} a_i) z^(r−|S|),
    R_empty=1.

The quadratic ∂_z^(r−2)F is

    (r!/2)z² +(r−1)! z sum_i R_i a_i
                    +(r−2)! sum_{i<j} R_ij a_i a_j.

After dividing its Hessian by the positive constant (r−2)!, the matrix in the order (z,a_1,...,a_r) is

    [ r(r−1)       (r−1)R^T ]
    [ (r−1)R           B    ],

with B_ii=0 and B_ij=R_ij. Its Schur complement at the positive top entry is

    B−((r−1)/r)RR^T = −N/r.

Thus this Hessian has exactly one positive eigenvalue and no other positive eigenvalues, for every finite graph and nonnegative weights. “Exactly one” follows from its strictly positive z² coefficient, even when every graph weight vanishes. This proves only this first-layer derivative condition. At r=3 it is the remaining ∂_z condition from the preceding note. It does not establish all derivative conditions, real-rootedness, a three-distinguished-element matroid extension, physical-role merging, or the general rank-six theorem.

The probability/Gram argument actually works for any r probability distributions, even without a common graph-weight representation. The graph assumptions enter only in the exact identification (4).

## Corroboration

The neighboring `check_general.py` independently recounts pair supports and checks (1), the Schur normalization and all three PSD matrices A−J/r, C−J/r and N exactly on finite rational examples. `check.py` separately exhausts small three-tail examples. These finite tests corroborate the ordinary proof; they do not supply a theorem premise.
