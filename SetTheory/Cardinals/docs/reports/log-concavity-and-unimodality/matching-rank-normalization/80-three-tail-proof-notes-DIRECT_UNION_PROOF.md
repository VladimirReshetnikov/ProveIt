# A direct matroid-union proof of the two-element Lorentzian transform

Status: submitted for final written review. The rank and six-case basis argument have already been independently reconstructed by root and both research reviewers. The earlier delivered proof remains unchanged.

## Attribution and scope

This short proof adapts the rank-compression transversal lift in the newly arrived manuscript `ProveIt_Weighted_Rank_Five/full_lift.tex`, inside `ProveIt_Weighted_Rank_Five_and_Two_Shore_Covers.zip`, to arbitrary matroids by matroid union. The incoming construction already proves the graph selected-left-marginal result and uses the same six plane/core cases, including the Boolean-union profile. It should be credited rather than presented as a newly discovered graph construction.

Pinned incoming archive: https://github.com/VladimirReshetnikov/ProveIt/blob/1512ef8356d10fef99e7caaa2753620f0c900c83/docs/incoming/ProveIt_Weighted_Rank_Five_and_Two_Shore_Covers.zip

Archive SHA256: 06dd0ae6a88654fb1f409dda35c3346c8cbd443a36d86f32fd1b0120903c6357. This is a verified intake source, not a claim that all its other results were audited or integrated. No literature-wide priority claim is made.

## Statement

Let M be any finite rank-q matroid on E union {A,B}, with A and B distinct. Loops, parallel elements and nonspanning E are allowed. Define the polynomials on the old variables w_e by

- U0 counts old q-subsets I that are bases of M;
- UA and UB count old (q−1)-subsets I for which I union {A}, respectively I union {B}, is a basis;
- U counts the union of those two families, each old subset once;
- V counts old (q−2)-subsets I for which I union {A,B} is a basis.

Negative-cardinality families are empty. U0 may be zero; it is not the basis polynomial of a lower-rank restriction.

Let L0,L1 be arbitrary nonnegative private-population masses, and let h_1,...,h_m be arbitrary nonnegative common-population weights. Set

    H=sum_j h_j,   S=sum_(j<k) h_j h_k,
    R0=L0+H,      R1=L1+H,
    mu=L0L1+H(L0+L1)+S,
    W=L1 UA+L0 UB+H U.

Then the following nonzero homogeneous degree-(q+2) polynomial is Lorentzian:

    F=z²U0+z(aR0+bR1)U0+ab mu U0
                    +z²(aUA+bUB)+abzW+abz²V.          (1)

All population quantities are parameters; the variables w_e,a,b,z remain independent.

## The union matroid

Adjoin new plane elements D={P1,P2,Z1,...,Zm}. Extend M to E union {A,B} union D by declaring every plane element a loop; call this extension M1.

On the same ground set let M2 be the rank-two transversal matroid with two slots, where

- A and P1 are adjacent only to slot1;
- B and P2 are adjacent only to slot2;
- each Zj is adjacent to both slots;
- every element of E is a loop.

The matroid union K=M1 union M2 exists, and its independent sets are exactly disjoint unions of an M1-independent set and an M2-independent set. Its rank is q+2: the sum of the two ranks gives an upper bound, while any M basis together with {P1,P2} is an independent set of that size. These sets are disjoint even when the M basis uses A or B.

Consequently each K basis admits a partition into an M1 basis of size q and an M2 basis of size2. All old E elements are forced into M1, and all plane elements are forced into M2. A basis is a ground-element subset, counted once, not once per such partition.

## Exact specialization

Assume mu>0. In the basis polynomial of K keep old variables w_e and distinguished variables a,b. Substitute

    P1=L1 z/mu,    P2=L0 z/mu,    Zj=h_j z/mu,

and multiply the resulting polynomial by the positive constant mu. Note the interchange of L0,L1 in the private-plane substitutions. The sum of weights of all feasible plane pairs is

    z²/mu² [L0L1+H(L0+L1)+S] = z²/mu.              (2)

Every pair of distinct plane elements is a basis of M2: there is one private element of each type, and all other plane elements are common. Classify a K basis by the numbers k of selected distinguished elements and ell of selected plane elements. Since old E contributes at most q elements, k+ell≥2; both k and ell are at most2. The only possibilities are the following six disjoint classes.

1. (k,ell)=(0,2): the old subset is an M basis, and the plane pair fills M2. Equation (2) and the outer factor mu give z²U0.
2. (1,1): if A is selected, it must fill M2 together with P2 or a common plane element; their total weight is R0 z/mu. The old subset is a basis. Similarly B gives R1. The contribution is z(aR0+bR1)U0.
3. (1,2): the plane pair fills M2, forcing the selected distinguished element into the M basis. The contribution is z²(aUA+bUB).
4. (2,0): A and B fill M2 and the old subset is an M basis. The contribution is ab mu U0.
5. (2,1): selecting P1 forces B into M2 and A into M1, giving L1 UA. Selecting P2 gives L0 UB. With a common plane element, feasibility holds if either A or B completes the old subset to an M basis. Even when both alternatives work, the same ground subset is only one K basis, so the coefficient is U, not UA+UB. This gives abzW.
6. (2,2): the plane pair fills M2 and both distinguished elements join the old subset in an M basis. The contribution is abz²V.

Their sum is exactly (1). No determinant weights, matching multiplicities, free-extension limit, Hessian induction or division by a homogenizing monomial is involved.

Every matroid basis polynomial is Lorentzian. Nonnegative linear substitutions and multiplication by a positive constant preserve this property. The specialization above therefore proves (1) when mu>0.

If mu=0, replace L0,L1 by L0+epsilon,L1+epsilon with epsilon>0. The perturbed mu is positive and the explicit right side of (1) converges coefficientwise to the desired polynomial. Closedness proves the limiting claim. The output cannot vanish: the coefficient of z² is exactly

    U0+aUA+bUB+abV,

the full original matroid basis polynomial, which is nonzero. Thus all ranks, zero population parameters, distinguished loops and nonspanning old sets are covered.

## Primary inputs and corroboration

- Matroid union and its independent-set definition: Bonin–Kung, “Semidirect sums of matroids,” Section2, https://arxiv.org/pdf/1210.0626. The proof uses the ordinary union theorem, not a stronger closure assertion.
- Matroid basis Lorentzianity, nonnegative substitutions and closedness: Brändén–Huh, “Lorentzian polynomials,” Theorems3.10,2.10,2.25, https://arxiv.org/pdf/1902.03719.
- Incoming graph lift credited above; the reformulation via union removes the need for a transversal representation of M.

The accompanying standard-library checker directly enumerates union basis subsets and tests the specialization on abstract matroids, including loops, nonspanning old sets and a nonrepresentable example. Zero-mu boundary coefficients are independently recovered by exact quadratic interpolation from three positive perturbations. These finite tests corroborate the ordinary all-size six-case proof and are not its premises.
