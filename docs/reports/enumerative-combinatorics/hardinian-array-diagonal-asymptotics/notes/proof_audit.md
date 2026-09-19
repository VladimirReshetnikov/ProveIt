# Proof audit and normalization checklist

## Claim

The leading asymptotic for every fixed r is proved in the manuscript, using the
published complementary-minor enumeration formula as the combinatorial input.
The formula gives an exact counterexample at r=7 to the suggested restriction on
prime factors of the leading constant (integer/rational powers interpretation).

## Dependency map

1. Array count = sum of complementary minors of M, M_ij=binom(i+j,i).
   External input: Dougherty-Bliss–Kauers, proof of Theorem 6.
2. M=B B^T, det M=1, B^{-1}=D B D.
   Binomial inversion and Vandermonde identity.
3. Jacobi and Cauchy–Binet => sum_U (sum_V det B[U,V])^2.
4. Pascal total nonnegativity => normalized row sum P belongs to [0,1].
5. Exact binomial likelihood ratio is a polynomial, including zero tails.
6. Cauchy–Binet in the polynomial degree index identifies the first surviving
   degree sum R=0+1+...+(r-1). All smaller degrees cancel algebraically.
7. Sub-Gaussian tails provide uniform exponential moments of normalized
   binomial variables; hence the Gaussian limit applies to Vandermonde moments.
8. The coefficient bounds are uniform for maximum deficit D=O(log L).
9. Outside that window, P<=1 and geometric weights give a vanishing tail even
   after multiplication by L^R. This justifies the limiting infinite sum.
10. The Gaussian factor is explicitly evaluated by an ordered-determinant
    identity and monic Hermite polynomials; the needed Pfaffian identity is proved.
11. The geometric Vandermonde partition function is a moment determinant with
    an explicit triangular-diagonal-triangular factorization.
12. Assemble factors with L=n-2 before converting L^{-R} to n^{-R}.

## Checks that prevent common wrong constants

- Matrix dimension N=n-1; largest Pascal row L=n-2.
- Sum of squares introduces 4^(rL), NOT 4^(rn) at the initial step.
- q=1/4, because a row deficit occurs twice after squaring.
- The absolute determinant expectation has factor 1/r!.
- I_r is an ordered Gaussian integral, not the unordered integral.
- det[binom(d_i,j-1)] = Delta(d)/product(j!).
- The ordered discrete Vandermonde sum has no extra 1/r! in its evaluation.
- Its product(j!)^2 cancels the factorial square from the confluent determinant.
- The Gaussian density has variance 1 and normalization 1/sqrt(2*pi).
- Row reversal and column permutations are absorbed in an absolute value;
  squared counts are independent of the overall sign.
- The uniform approximation retains I_{r,L} until the weighted sum is controlled.

## Exact finite determinant

sum_r H_r(n,n) t^r = det(I+t(A+v v^T)),
A=B J B^T, v=(1,2,...,2^(N-1)), J_ij=sign(j-i).
Even coefficients arise from Pfaffians of A; odd coefficients require the
bordered skew matrix. A determinant lemma combines the two. The leading
coefficient is 1 because J+11^T is upper triangular with diagonal 1.

## Additional probability statement

The distribution on row subsets weighted by squared minor sums has a total-
variation limit proportional to (1/4)^sum(d) Delta(d)^2. It is an auxiliary
measure on the positive representation; no undocumented bijective statistic
on original arrays is asserted. Its total deficit minus binom(r,2) is negative
binomial of shape r^2. Moment convergence is justified by applying the same
normalization theorem at a nearby geometric parameter q'>q.

## Limits of the result

- Fixed r only; no bound uniform in growing r is claimed.
- Leading asymptotic only; no full Edgeworth or inverse-power expansion claimed.
- A radial logarithmic generating-function statement is proved, not a complete
  complex singular expansion or automatic analytic continuation.
- The guessed r=3 minimal recurrence is not proved here.
- The known D-finiteness of fixed-r diagonals is not claimed as new.
- Numerical ratios neither prove the limiting constant nor a rate of convergence.
- No formal proof assistant, peer reviewer, or independent novelty search has
  certified the result.
