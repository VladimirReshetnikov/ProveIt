# Independent audit of the all-power trigamma recurrence

I derived the recurrence without using the exact-check implementation.

1. The backward difference means Delta A_n^d=A_(n-1)^d-A_n^d, with A_(n-1)=A_n+h, h=n^-2. The Bernoulli identity in the parent message is correct. It follows by the polynomial identity for the trapezoidal derivative sum, or directly by comparing powers of A/h; the even Bernoulli coefficients and the minus sign are correct. The formal j=d/2 term is harmless because Delta A^0=0.

2. The safest cutoff for the centered M moments is n=0,...,N-1, not n=0,...,N. For every even integer q>=0,
   sum_(n=0)^(N-1)(n+1/2)^q=(B_(q+1)(N+1/2)-B_(q+1)(1/2))/(q+1),
   whose N^0 coefficient is zero. Hence the CT of the centered original moment equals the ordinary polynomial-subtracted M. If n=0,...,N is used instead, one must retain a nonzero endpoint polynomial; omitting it would be an error.

3. With p=k-2>=0, the exact shift identity is
   sum_(n=1)^N n^p(A_(n-1)^(d-1)+A_n^(d-1))
   =sum_(n=0)^(N-1)[(n+1)^p+n^p]A_n^(d-1)
     +N^p A_N^(d-1)-delta_(p,0)A_0^(d-1).
   Expanding the bracket around x=n+1/2 gives precisely the coefficient of cosh(t/2)G_(d-1), including the factor d and the exception -(d/2)delta_(k,2)zeta(2)^(d-1).

4. The boundary combination is
   [u^k]{A^d+(d/2)u^2 A^(d-1)+sum_(j>=1)binom(d,2j)B_(2j)u^(4j)A^(d-2j)}
   =[u^k]u^(2d)B_d(1+A/u^2)
   =[u^k]u^(2d)B_d(1/2+E/u).
   The Bernoulli convention B1=-1/2 is essential: B1(1)=+1/2 supplies the positive d/2. Since B_d(1/2+z) has parity d and E(u) is even, the boundary combination vanishes when k has parity d+1. This proves the cancellation for every required coefficient.

5. The regular moment parity is correct. If m≡d mod2, the leading unsubtracted exponent m-d is even. Removing the nonnegative powers leaves O(x^-2), or faster if no subtraction is needed. The continued Hurwitz counterterms vanish because zeta(-2j,1/2)=0, including j=0. Thus M is an ordinary absolutely convergent sum.

6. For e>=1 and h<=0, C_e,h is an ordinary convergent minimum-index sum because Delta A_n^e=O(n^(-e-1)). Grouping the ordered e-tuples by their distinct descending indices gives coefficient e!/prod c_i! and index word (2c_1,...,2c_(l-1),2c_l-h). This proves the claimed composition formula directly. C_e,0=zeta(2)^e also follows by telescoping. The even-d anchor C_d,1 is convergent for d>=2; its possible final MZV index1 is admissible because the first index remains>=2. The excluded d=1,k=1 case would diverge, so retaining the restriction matters.

Conclusion: no flaw identified in the proposed recurrence, parity cancellation, or ordinary-sum interpretation. This is an independent analytic audit, not merely a rerun of the 220 exact fixtures.
