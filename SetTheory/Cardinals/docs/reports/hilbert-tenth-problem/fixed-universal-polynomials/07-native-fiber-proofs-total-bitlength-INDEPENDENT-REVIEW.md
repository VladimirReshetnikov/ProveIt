# Independent review of the total coordinate bitlength law

Date: 2026-10-03

## Scope and conclusion

I independently read the entire-fiber classification and the previous unsmoothed second-term theorem in the two frozen upstream packets. I reviewed the final THEOREM.md total-bitlength law for that already classified fiber, including the exact-energy proof used there and the equivalent comparison-energy proof recorded below. This review is conditional on those classification hypotheses; it does not reprove the pinned source's soundness or execute any upstream code.

The final artifact is approved. Its SHA-256 at review time is:

    473aa94b5be11074a7abf00484711b72e56feb8f49f20b27f8d9a38b170138a1

The leading and square-root coefficients are correct:

    kappa_sum = 1/[M(3p−2)lambda]
                + sum_(l>=1) 1/[6Ml beta_(Ml)],

    N_sum(B) = kappa_sum (log 2) B
               + zeta(1/2) sqrt(log 2)/(M sqrt(3lambda)) sqrt(B)
               + O(B^(1/3)).

The law is valid for the ordinary unsmoothed inclusive cutoff, including exact integer bitlength boundaries and ties. The exact beta values must be retained in the leading coefficient. I found no mathematical defect in the reviewed artifact. I also checked the exact relation to the previous maximum-height coefficient, its explicit error constants, its reciprocal-series tail bound, and its ranked-bit inversion. The derivation and boundary audit follow.

## 1. Exact algebra and positivity

The five varying supplied coordinates are

    f, i=R/c², j=(U+p)/c, o=(U+c)/f, y.

The upstream classification already proves that all five are positive integers at every allowed pair. Direct cancellation, with no approximation, gives

    P := f i j o y = R y (U+p)(U+c)/c³.

Thus f cancels from the product. This does not remove its own bit cost: rounding the five separate logarithms leaves a bounded correction, addressed below.

Set beta=arcosh R. Then

    R=cosh beta,
    y=sinh(n beta)/sinh beta,
    U=cosh(n beta)/cosh beta.

In particular U>=1 for n>=1. The allowed native indices have n>=p>=3, beta>=M lambda>0, and c>0, so all logarithms used here are defined. Positivity does not rely on an approximation to U, j, or o.

## 2. An exact logarithmic identity and its uniform bound

Expansion of the preceding hyperbolic expressions yields the exact identity

    log P = (3n−2) beta − log(2c³)
      + log[(1−exp(−2n beta))(1+exp(−2n beta))²
                /(1−exp(−4beta))]
      + log(1+p/U) + log(1+c/U).

Write q=M lambda>0 and t=exp(−2q)<1. Since n>=1 and beta>=q, the logarithmic fraction in this identity lies between log(1−t) and 2log 2−log(1−t²). The last two terms lie between zero and log(1+p)+log(1+c). All fixed quantities may depend on the prescribed native ports and scale. Consequently

    log P = (3n−2) beta + O(1)

uniformly over every allowed m,n. The bound does not grow with n or m. This is the essential uniformity: replacing beta by m lambda at this stage would produce an error of order n, which is unsuitable for bounded-cutoff comparison.

## 3. Separate coordinate bitlengths and a global sandwich

For a positive integer x, define b(x)=floor(log_2 x)+1. Let F be the sum of b(x) over the seventeen fixed supplied coordinates, and let S be the total bitlength over all twenty-two coordinates. Then exactly

    S = F + log P/(log 2) + delta,
    delta = sum_(x in {f,i,j,o,y}) [1−{log_2 x}],
    0<delta<=5.

The value 1, not 0, is contributed by a coordinate that is a power of two. Thus powers of two need no exceptional convention. Combining this identity with the uniform product-energy bound gives a constant C such that

    |(log 2)S−E0(m,n)|<=C,
    E0(m,n)=(3n−2) beta_m.

Let G(T) count all allowed pairs with E0<=T, using an inclusive cutoff. For every sufficiently large real B,

    G((log 2)B−C) <= N_sum(B) <= G((log 2)B+C).

Both implications use weak inequalities, so exact cutoff equalities are included correctly. No stability of any individual floor, no equidistribution, and no bound on individual tie multiplicities is assumed. This sandwich is preferable to summing coordinatewise rounding discrepancies over all rows.

## 4. Hyperbola calculation for the exact comparison energy

Write beta_l=beta_(Ml), q=M lambda, b=(log Delta)/2. The frozen estimates give

    ql<=beta_l<=ql+b.

The baseline n=p has E0=(3p−2)beta_l, and hence contributes

    T/[M(3p−2)lambda]+O(1).

For n=4Mlk+sigma p, with sigma=+1 or −1, write

    E_sigma(l,k)=a_l k+h_sigma beta_l,
    a_l=12Ml beta_l,
    h_sigma=3sigma p−2,
    a=12lambda M².

Every allowed E_sigma is positive. For the negative branch this follows already from n>=p>=3. Uniformly in positive l,k,

    a_l=a l²+O(l),
    1/a_l=1/(a l²)+O(l^(−3)),
    |E_sigma(l,k)−a k l²|<=C1 k l.

One admissible constant is C1=12Mb+(3p+2)(q+b). Positivity then gives the displacement estimate

    |sqrt(E_sigma(l,k)/(ak))−l|<=C1/a=:D.

For a fixed row, the exact count is

    max(0, floor((T−h_sigma beta_l)/a_l))
       = T/a_l+O(1),

uniformly for l>=1, T>=0. Clipping at zero causes no difficulty because h_sigma beta_l/a_l=h_sigma/(12Ml) is bounded. For a fixed column, restricted to l>L, the displacement bound gives

    #{l>L:E_sigma(l,k)<=T}
      = (sqrt(T/(ak))−L)_+ + O(1),

uniformly in k,T,L. This count sandwich, rather than a perturbed-floor substitution, handles arbitrarily close boundary points.

Choose L=floor(T^(1/3)), X=T/a, K=floor(X/L²). The initial L rows contribute T sum_(l<=L)1/a_l+O(L). Columns above K can contribute only up to X/(L+1−D)². That latter cutoff differs from X/L² by O(X/L³)=O(1), and every such extra column has O(1) admitted rows. Hence all boundary columns together contribute O(1). For the first K columns beyond the row cutoff one obtains

    sqrt(X) sum_(k<=K) k^(−1/2)−LK+O(K+1).

Using

    sum_(l>L)1/a_l=1/(aL)+O(L^(−2)),
    sum_(k<=K)k^(−1/2)=2sqrt(K)+zeta(1/2)+O(K^(−1/2)),

and the exact cancellation

    2sqrt(XK)−LK−X/L = −L(sqrt(K)−sqrt(X)/L)²,

gives separately for each sign

    Q_sigma(T)=T sum_(l>=1)1/[12Ml beta_l]
      + zeta(1/2)/(sqrt(12lambda) M) sqrt(T)
      + O(T^(1/3)).

All error terms are O(T^(1/3)); the displayed cancellation error is O(1). The two signs and the baseline are disjoint by the existing classification. Adding them proves

    G(T)=kappa_sum T
      + zeta(1/2)/(M sqrt(3lambda)) sqrt(T)
      + O(T^(1/3)).

The coefficient series converges absolutely, since beta_l>=M lambda l. Its exact terms must be kept until after the coefficient is extracted; replacing them by the quadratic model globally would change the coefficient of T.

## 5. Transfer to actual bitlength and optional ranking

Applying the preceding estimate to the two cutoffs in the global sandwich proves the proposed law with T=(log 2)B. Fixed shifts change the linear term by O(1) and the square-root term by O(T^(−1/2)), so they are absorbed in the stated remainder. This also proves the law uniformly at every integer B.

If S_v is the v-th total bitlength, with multiplicity and arbitrary ordering within equal-bitlength ties, then

    N_sum(S_v−1)<v<=N_sum(S_v).

Applying the count at these two arguments proves the usual inversion without a tie hypothesis. With A_sum=kappa_sum log 2 and D_sum=zeta(1/2)sqrt(log 2)/(M sqrt(3lambda)),

    S_v=v/A_sum−D_sum A_sum^(−3/2)sqrt(v)+O(v^(1/3)).

The square-root correction in this inversion is positive because zeta(1/2)<0.

## 6. Independent exact auxiliary checks

The companion ../../check_total_bitlength_review.py is newly written and imports no upstream code. It tests the auxiliary parameters A=3, p=3, c=35, M=105, with l=1,2,3 and n=p,4Ml−p,4Ml+p. These satisfy the algebraic Pell reconstruction used in the tests; they are not claimed to be complete padded native witnesses or to satisfy the native source's large-index bootstrap hypothesis.

The checks verify positivity and integrality of all five coordinates, both varying norm equations, the exact product cancellation, and the exact integer consequence

    0 <= sum b(x)−b(product x) <= 4.

Three direct fixtures include the power-of-two rounding boundary. The script uses explicit exceptions rather than Python assert statements, so checks remain active under python -O.

Both normal and optimized Python runs pass all nine exact auxiliary tuples and all three direct rounding fixtures. The largest tested varying-coordinate bit sum is 3,039,353 bits. The tests are secondary evidence; the uniform proof above and the prerequisite classification are the basis of approval.
