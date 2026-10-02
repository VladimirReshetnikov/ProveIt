# Independent mathematical audit: L-convex area asymptotics

Date: 2026-10-01. Status: substantive analytic and algebraic checks passed.

Audited source: proof-note.md

SHA-256: 17b92af4f7d9f8472f3c7cf78f6e98d7d95131cb84bf70144e339fd5fe64ff56

This verdict applies to that exact source revision. Later presentation formats should be compared with it before delivery; any changed formulas or new claims require a corresponding check.

## Scope and verdict

This audit takes the area generating function in Guttmann–Kotěšovec (2023), Eq. (1.1), as its enumerative premise. The question checked is whether its coefficients rigorously satisfy the proposed asymptotic, including the prefactor and a Poincaré expansion to every fixed order. Numerical agreement is not used as proof.

No substantive defect was found in the exact decomposition, its whole-circle bounds, the local expansion, the stated coefficient formula, or the displayed inverse polynomials. The decisive point is the uniform bound for the residual on the entire Cauchy circle; the argument is not a radial-asymptotic-to-coefficient inference.

## Independently checked details

1. **Generating-function indexing.** With f_{-1}=f_0=1 and h_n=f_{n-1}/(q;q)_n, the recurrence gives (1-z)^2 H(z)=(1+qz^2)H(qz)-z for |z|<1. The n=1 equation gives h_1=1/(1-q), and the n=2 equation gives f_1=1+2q-q^2, so no index shift is hidden. The products defining the homogeneous solution are correct.

2. **Analytic convergence.** Writing c_k=2q^k-q^{2k}, the recurrence implies f_n=1+sum_{k=1}^n(n-k+1)c_k f_{k-2}. Dividing by n+2 and using the summability of k|c_k| gives f_n=O_q(n) by discrete Gronwall. Consequently H is analytic for |z|<1, and the q-binomial rearrangements are absolutely convergent for fixed |q|<1. The boundary factor B is evaluated through its convergent product-series expression, not by substituting z=1 into the divergent H series.

3. **Exact remainder.** Independent substitution of the homogeneous solution into the area sum gives A=PBD+R, with R=1+E/(q;q)_infinity and exactly the E printed in the proof note. The apparent extra -1 in the intermediate j sum vanishes because sum_j (-1)^j q^{j(j-1)/2}/(q;q)_j=(1;q)_infinity=0. This cancellation is exact and does not enter the absolute-value bound for E.

4. **Heine and Fine identities.** The substitutions were checked directly against DLMF 17.6.6 and 17.6.10. Heine gives S=sum_n b^n/(1-aq^n), where a+b=0 and ab=q. Fine with alpha=a/q^2, beta=a/q, z=b gives (V-aV_q)/(1-a)=(1-b)[1+(b-1)S]. Interchanging a and b cancels V_q and proves D=1-S=B. The hypotheses |a|=|b|=sqrt(|q|)<1 ensure the needed convergence; q=0 follows by continuity.

5. **Partial-theta expression.** The double sum for S is absolutely convergent. Splitting it into the diagonal and the paired off-diagonals gives B=1-sum_{k>=0}q^{k(k+1)}(1-q^{2k+1})/(1+q^{2k+1}). There is no missing factor of two, sign, or exponent shift.

6. **Uniform residual estimate.** For r=|q|=e^{-t}, direct product bounds give

   |R(q)| <= 1 + [2/(1-r)] (-r;r)_infinity^3 / [(r;r)_infinity(r;r^2)_infinity].

   Equivalently, the second term is [2/(1-r)] (r^2;r^2)_infinity^4/(r;r)_infinity^5. Its radial product asymptotic is O(t^{-1/2} exp(pi^2/(2t))). This inequality holds for every argument of q, including neighborhoods of roots of unity. Its exponential constant pi^2/2 is strictly smaller than kappa=13pi^2/24.

7. **Global B bound.** The theta expression gives |B(q)|=O(t^{-1}log(1/t)) uniformly on |q|=e^{-t}. For instance, use 1/(1-e^{-x})<=1+1/x and split the resulting Gaussian harmonic sum at k of size t^{-1/2}. Thus B cannot offset an exponential minor-arc saving.

8. **Minor arcs.** On the denominator block ceil(1/t)<=j<=floor(2/t), r^j is bounded away from both zero and one. Each factor gives a fixed multiple of 1-cos(j theta) in the logarithmic saving. The sum is bounded below by c min(theta^2/t^3,1/t): for |theta|<=t/4 use the elementary quadratic cosine bound; for t/4<=|theta|<=Ct use a uniform Riemann sum on a compact interval; for |theta|>=Ct use the geometric-series bound and choose C large. This covers the entire interval [-pi,pi], with no unexamined roots-of-unity arcs.

9. **Uniform local D expansion.** For z=t+iy, 0<t<=0.1, |y|<=t/8, set x=(j+1)t. The summand ratio has modulus at most e^{0.1}sqrt(65)/(8e) when x<=1 and at most e^{0.1}/(e-1) when x>=1. Both are less than 2/3. Hence the tail starting at j=M is O(|z|^M) uniformly, since its initial term has a zero of order M. Finite-term Taylor expansion is therefore a valid all-orders sectorial Poincaré expansion. It is not a claim that the formal infinite Taylor series converges.

10. **Eta normalization.** P=(q^2;q^2)_infinity^2/[(q;q)_infinity^4(q^4;q^4)_infinity]. Eta inversion yields

   P(e^{-z})=(z/(2pi))^{3/2} exp(13pi^2/(24z)-z/6)(1+O(exp(-c/t)))

   uniformly in the preceding wedge, with the principal power of z. The coefficient exponent, amplitude, and shift -1/6 are all correct.

11. **Coefficient transfer.** Put N=n-1/6, t=sqrt(kappa/N), and use the Cauchy circle |q|=e^{-t}. Outside |arg q|<=t^{3/2}log(1/t), the principal term is smaller than every algebraic relative order. The entire residual is exponentially smaller. Inside that arc, an O(z^M) amplitude error contributes O(t^M) relatively, by the Gaussian bound exp(-c theta^2/t^3). This proves the claimed error O(N^{-M/2}) for each fixed M.

12. **Bessel coefficient formula.** For alpha=3/2+m, the local model integral z^alpha exp(kappa/z+Nz) agrees to all algebraic orders with (kappa/N)^((alpha+1)/2) I_{-alpha-1}(2sqrt(kappa N)). One rigorous comparison deforms the local vertical segment to the major arc of |z|=t and completes a Hankel contour around the negative real axis. On the circle the phase is 2sqrt(kappa N)cos(phi); on the negative rays z=-s, s>=t, it is -kappa/s-Ns<=-2sqrt(kappa N). The remaining arcs and connectors are superalgebraically negligible. Expanding exp(kappa/z) on that contour also gives the result directly through the reciprocal-Gamma Hankel integral. The half-integral Bessel expansion terminates at k=m+2. The note's c_r formula and its displayed c_0 through c_4 follow with the stated signs and factorials.

13. **Leading constant.** The leading amplitude is (1/4)(2pi)^{-3/2}. Gaussian transfer multiplies this by kappa/(2sqrt(pi)), giving 13sqrt(2)/768 exactly. No fitted numerical constant is used. The introduction of the 2023 paper agrees; its final display in Section 2 reciprocates the prefactor and is inconsistent with the introduction.

14. **Inverse expansion.** The displayed h_1 through h_4, logarithmic coefficients ell_1 through ell_4, and the polynomials P_1 through P_3 were checked by formal substitution. All agree. The discrete threshold inverse needs an O(1) rounding allowance. The note states that allowance correctly. Eventual strict monotonicity follows already from the coefficient expansion with relative error O(n^{-1}), since the leading adjacent-ratio increment is positive of order n^{-1/2}. The additional row-enlargement injection is also valid using nested row intervals and column convexity.

## Sources consulted

- Guttmann–Kotěšovec (2023), arXiv:2109.09928v3, Eq. (1.1), introduction, and final Section 2 display: https://arxiv.org/pdf/2109.09928
- Heine's first transformation: https://dlmf.nist.gov/17.6#E6
- Fine's second transformation: https://dlmf.nist.gov/17.6#E10

## Scope limitations

This is a mathematical audit of the supplied argument, not independent peer review, a claim that the result is already published, or a fresh combinatorial proof of the starting generating function. The numerical scripts provide useful regression checks but are unnecessary to the analytic proof.
