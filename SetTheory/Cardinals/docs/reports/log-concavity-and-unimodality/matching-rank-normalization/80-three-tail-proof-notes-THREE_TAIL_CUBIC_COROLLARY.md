# The full three-tail rank-zero polynomial is Lorentzian

Status: submitted for independent review. This is an ordinary corollary of the approved all-r first-layer lemma and the published rank-three Rayleigh theorem; no finite coefficient certificate is a premise.

Let P={0,1,2} be the left shore of any finite bipartite graph, with arbitrary nonnegative activities on the right shore. Let R_S count feasible head subsets matching S once, weighted by the product of their activities. Then

    F(z,a)=z³+z² sum_i R_i a_i+z sum_(i<j) R_ij a_i a_j
                +R_012 a_0 a_1 a_2

is Lorentzian, retaining each of the three selected-tail variables individually. Left activities may additionally be incorporated by nonnegative scaling of those variables.

## M-convex support

Delete zero-weight heads. The matchable subsets of P are the independent sets of a transversal matroid L on P, possibly of rank less than three. Take the direct sum of L and the free matroid on three new dummy elements, and truncate to rank three. Its bases are exactly I union D', where I is independent in L and |D'|=3−|I|. The basis polynomial is Lorentzian. Identify the three dummy variables with z; the resulting polynomial is Lorentzian and therefore has M-convex support. Its support is exactly that of F. Its coefficients need not equal those of F: only this support equality is used. This construction also handles isolated tails and an empty positive-weight graph.

## The three selected-tail derivatives

Use another transversal matroid K, now on the original heads plus three private dummy elements d_i, with the three left vertices as matching slots. Each d_i is adjacent only to slot i. Its rank is exactly three because the three dummies form a basis. After substituting the given head activities, its basis polynomial is

    B(d)=d_0d_1d_2+sum_i R_i product_(j≠i)d_j
                  +sum_(i<j) R_ij d_k+R_012,

where k is the remaining index. Every basis is a head subset together with exactly the dummies of unused slots, so these coefficients count supports once.

Wagner's Theorem 1.1 states that every rank-three matroid is Rayleigh. Set d_i=0 by a nonnegative boundary limit and take the Rayleigh difference in d_j,d_k. Since

    B|_(d_i=0)=R_i d_jd_k+R_ij d_k+R_ik d_j+R_012,

that inequality is exactly

    R_ij R_ik − R_i R_012 ≥0.                       (1)

The zero head activities follow by continuity, or by deleting them before constructing K. Thus there is no positive-activity gap in (1).

The Hessian of ∂_(a_i)F in (z,a_j,a_k) is

    [[2R_i,R_ij,R_ik],
     [R_ij,0,R_012],
     [R_ik,R_012,0]].

Its determinant is 2R_012(R_ijR_ik−R_iR_012)≥0. If R_012>0, its bottom 2-by-2 principal block has one positive and one negative eigenvalue. The determinant then forces the third eigenvalue to be nonpositive. If R_012=0, it is an arrow matrix with zero bottom block, which directly has at most one positive eigenvalue. The unused coordinate a_i contributes only a zero row and column.

## The remaining derivative

The approved GENERAL_FIRST_LAYER.md with r=3 proves that Hess(∂_z F) has at most one positive eigenvalue. We have now checked every first derivative of this cubic. Nonnegative coefficients, M-convex support and the quadratic-Hessian characterization prove that F is Lorentzian.

This result is restricted to a three-vertex left shore (the rank-zero old-matroid base). It does not contradict the positive-rank three-marked matroid and 3+3-cover counterexamples. No real-rootedness or stronger physical-role-collision claim is made.

## Primary references checked directly

- David G. Wagner, “Rank three matroids are Rayleigh,” The Electronic Journal of Combinatorics 12(1) (2005), Note N8, DOI 10.37236/1975. Theorem 1.1 and the defining Rayleigh difference are in the primary manuscript: https://arxiv.org/pdf/math/0403216 (printed page 2). The theorem is used only at this stated rank and for nonnegative specializations by continuity.
- Petter Brändén and June Huh, “Lorentzian polynomials,” https://arxiv.org/pdf/1902.03719. Theorem 3.10 supplies matroid basis Lorentzianity, Theorem 2.10 supplies nonnegative linear substitutions, and Theorem 2.25 supplies the M-convex-support/quadratic-derivative characterization.
