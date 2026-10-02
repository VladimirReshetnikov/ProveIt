# Real stability when one balanced core edge is missing

Status: independently approved, including arbitrary-class symbolic identities and final written-note review, on October 1, 2026. Separate from the approved complete-core and star-core notes. No priority claim.

## Theorem

Let P={p1,p2}, Q={q1,q2}, and let I be independent exterior vertices with arbitrary arcs P→I and I→Q. The core contains p1→q1, p1→q2, p2→q1, and omits p2→q2. There are no other arcs. With arbitrary nonnegative independent tail and head activities, the signed physical-vertex monomer polynomial is real stable. Thus the directed support polynomial has only negative real roots and is rank-ULC at its actual degree. Relabeling and reversal are included; transitivity is unnecessary.

## Corrected split-copy kernel

Use the rank-two side basis polynomials B_P,B_Q and element sums L_P,L_Q from the approved complete-core proof. Isolated exterior copies are excluded from the side matroids and contribute only monomer factors. Let r_P be the parallel-class sum consisting of dummy p1 and the head copies private to p1. Let r_Q consist of dummy q1 and the tail copies private to q1. The split signed kernel is

    H = B_P B_Q − L_P L_Q + 1 + r_P r_Q.

Zero-core-edge supports are unchanged. A one-core-edge support is lost exactly when its residual unmatched source and sink are forced to be p2 and q2. On the source side this means either p1 is unused (its dummy), or both sources occur with an exterior head private to p1; these possibilities give r_P. A head adjacent to both sources does not force p2 to be the residual source, so it is correctly excluded. The sink side is the identical statement with r_Q. These lost supports had negative signed contribution, accounting for +r_P r_Q. Two-core-edge supports still have the off-diagonal matching p1→q2,p2→q1 and contribute +1 once. Hence the formula counts endpoint supports once, not witnesses.

## Abstract stable coupling

The following is stronger than the particular side-matroid application. For any two loopless rank-two matroids, write their parallel-class sums as

    p0,p1,...,pa  and  q0,q1,...,qb,

where p0=r and q0=s are distinguished classes. In these independent class variables put

    P=e2(p), Q=e2(q), L=sum(p), M=sum(q),
    H=P Q−L M+1+r s.

We prove H real stable by the multiaffine Rayleigh criterion: a nonzero real multiaffine polynomial is real stable iff every difference Δ_xy=(∂xH)(∂yH)−H∂x∂yH is nonnegative at every real assignment. See Wagner's survey, Theorem3.1, citing Brändén's Theorem5.6 and Wagner–Wei's Theorem3. Note that this is the all-real criterion, stronger than positivity only on the positive orthant.

There are five pair types up to interchanging the two sides and permuting nondistinguished classes. Empty sums below are zero. Each identity follows by expansion and e2(z)=((sum z)^2−sum z^2)/2. Consequently they hold for any number of classes.

### 1. Same side, one distinguished: x=p0, y=pi, i>0

Let A=sum_{k≠0,i}p_k, U=sum_{k≠0,i}p_k², B=sum_{l>0}q_l, V=sum_{l>0}q_l². Then

    2 Δ_xy = (Q A−B)² + Q² U + V.

### 2. Same side, neither distinguished: x=pi, y=pj, i,j>0

Let A=sum_{k≠i,j}p_k, U=sum_{k≠0,i,j}p_k², V=sum_{l>0}q_l². Then

    2 Δ_xy = (Q A−M)² + (Q r−s)² + Q² U + V.

### 3. Opposite sides, both distinguished: x=p0, y=q0

Let A=sum_{k>0}p_k, U=sum_{k>0}p_k², B=sum_{l>0}q_l, V=sum_{l>0}q_l². Then

    2 Δ_xy = A² V + B² U.

### 4. Opposite sides, one distinguished: x=p0, y=qj, j>0

Let A=sum_{k>0}p_k, U=sum_{k>0}p_k², B=sum_{l≠j}q_l, V=sum_{l≠0,j}q_l². Thus B includes s. Then

    4 Δ_xy = [A(B+s)−2]² + A² V + U[(B−s)²+V].

### 5. Opposite sides, neither distinguished: x=pi, y=qj, i,j>0

Let A=sum_{k≠i}p_k, U=sum_{k≠0,i}p_k², B=sum_{l≠j}q_l, V=sum_{l≠0,j}q_l². Thus A includes r and B includes s. Then

    4 Δ_xy = (A B−r s−2)² + (A s−r B)²
              + U(B²+s²) + V(A²+r²) + U V.

Every displayed expression is a sum of squares after distributing U and V. They are therefore nonnegative for all real assignments. The constant term1 makes H nonzero, so the Rayleigh criterion proves stability. Replacing each class variable by the sum of its individual matroid-element variables preserves stability, since a nonempty sum of upper-half-plane arguments is upper-half-plane. Thus H is stable in all original side variables.

## From the kernel to the directed support polynomial

Give core dummies their core monomer variables and substitute −1/z_x for each active exterior-copy variable. Multiply by the product Z of all exterior-copy monomer variables, including isolated copies. The corrected support identity above says that ZH is precisely the split signed monomer polynomial. Multiaffinity cancels denominators and negative reciprocal substitution preserves the upper half-plane.

Introduce positive split-vertex activities using μ(z)↦(∏w_i)μ(z_i/w_i), with the physical tail activity on each tail copy and the physical head activity on each head copy. For each pair of exterior copies apply the physical merge ab↦z, a↦1, b↦1, 1↦0. Its symbol z+u+v is stable, so the finite-degree Borcea–Brändén theorem proves stability after every merge. This retains unused vertices and either single-used role, and excludes simultaneous use. The empty-support monomial has coefficient1 throughout. Zero activities follow by continuity without a zero-polynomial exception.

Finally μ(t,...,t)=t^N Γ(−t^(−2)) is real rooted, so every root of Γ is negative real. Newton's inequalities give ULC at the actual surviving degree. These final steps are exactly the independently approved steps of ../BALANCED_REAL_ROOTEDNESS_PROOF.md; no new normalization assumption is introduced.

## Checks and sources

- verify_rayleigh_squares.py checks all five identities by exact symbolic expansion with four arbitrary class variables on each side. The identities above, not a bounded class test, give the arbitrary-class proof.
- verify_incomplete_kernels.py independently recounts ordered disjoint endpoint supports using all Hall inequalities, compares the exact weighted physical monomer coefficients, and includes isolated copies and zero activities. See incomplete_kernel_verification.json. These checks supplement the proof.
- D. G. Wagner, *Multivariate stable polynomials: theory and applications*, Theorem3.1 (all-real multiaffine Rayleigh criterion) and Theorem5.2 (plus-sign symbol theorem): https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf .
- J. Borcea and P. Brändén, *The Lee–Yang and Pólya–Schur Programs. I. Linear Operators Preserving Stability*, Inventiones Mathematicae177 (2009),541–569, Theorem1.1: https://arxiv.org/abs/0809.0401 .
