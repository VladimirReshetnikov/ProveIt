# Focused proof audit

## Definition and combinatorics

For fixed row n, the k-th coefficient counts partitions of n+(r−1)k labels.
At k=1 this is n+r−1 labels and there is exactly one partition, for n>=1.
At k=2 the label count is N=n+2r−2. Choosing one of the two blocks counts
an unordered partition twice, including when the block sizes agree.
The two forbidden binomial tails are disjoint for N>=2r−1. At n=1 the
middle range is empty and the two tails exhaust all 2^N subsets.

The independent verification counts the full block containing label 1,
not the single-label deletion used by the triangle recurrence. This checks
the same objects by a different decomposition.

## Degree-five extraction

After factoring x out of each of three rows, the constant matrix is J,
the all-ones matrix. With

    L = [[1,0,0], [-1,1,0], [0,-1,1]],

both det(L)=1 and L J L^T=diag(1,0,0). The lower-right block of L B L^T
is [[Delta^2 b_a, Delta^2 b_(a+1)],
    [Delta^2 b_(a+1), Delta^2 b_(a+2)]].
Its determinant supplies degree two of the transformed determinant, hence
degree five before factoring. Terms from the first row/column outside the
corner have degree at least three after factoring. Coefficients in the
original polynomials at degree three and higher do not enter the answer.

## Binomial-tail cancellation

With m=r−3, N=a+2r−2, B=2^(N−1), and F_j=F_m(N+j),

    (B−F_0)(4B−F_2) − (2B−F_1)^2
    = −B(F_2−4F_1+4F_0) + F_0 F_2−F_1^2.

Pascal's identity turns the parenthesis into
binomial(N,m)−binomial(N,m−1). It is positive at the required N>=2m+5.
The partial-binomial-sum Turan determinant is nonpositive by decreasing
successive ratios. Hence the full expression is strictly negative,
including m=0 where the partial-sum determinant is exactly zero.

No sign inequality is reversed when denominators are cleared: all ratios
used in the argument have positive denominators in the stated ranges.

## First-shift factorization

With A=binomial(2r−1,r−1), the normalized second differences are

    u, 1+v, 2+u+w,

where u,v,w are the three displayed positive rational functions of r.
The numerator after putting u(2+u+w)−(1+v)^2 over the denominator
(r+1)^2(r+2)^2(r+3) factors as

    −(r−2)(r−1)(r+1)(r^2+11r+6).

Cancellation of r+1 is legal for every positive integer r. The normalized
factor also equals 1−24r(2r+1)/((r+1)(r+2)^2(r+3)) before the overall
negative A^2; this confirms its limit one and that it lies in (0,1) at r>=3.
The optional SymPy script verifies the main rational identity formally.

## Moment statements

A negative coefficient alone need not give a negative specialization.
Here it is the first nonzero coefficient, which does. The norm bound
M gives a rational interval without relying on approximate root finding.

Shift a=1 is a Gram matrix only after weighting by t, so it excludes a
positive measure on [0,infinity), not automatically one on the entire
real line. Shift a=2 is the Gram matrix of t,t^2,t^3 for any real positive
measure and therefore yields the Hamburger obstruction. These two uses
are kept separate throughout.

## Boundaries and exclusions

The shift-zero polynomial s_(r,0)=1 is outside the common-x-factor
hypothesis. At r=1,2 the second differences are geometric and the
x^5 coefficient is zero, not negative. No positive result is inferred
merely from that vanishing. The full positive cases are explicitly imported.

No determinant is ever divided by. Integrality follows from integer
polynomial coefficients; no generic-parameter or nonsingularity assumption
is hidden in the factored formulas.
