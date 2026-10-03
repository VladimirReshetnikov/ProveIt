# A268485 / A047909: quantitative Beta-renewal transition

Status: mathematical research draft, 2 October 2026. The exact renewal interpretation and Gaussian limit are established prior work of El Maazouz–Pitman (see SOURCES.md). The contribution explored here is the explicit arbitrary-finite-order central expansion, its diagonal specialization, and inversion. No claim that the older Gaussian or moment conjectures are newly solved is made. The literature search found no such quantitative expansion, but that is a bounded search result, not a universal novelty certification.

## 1. Exact quantity and renewal reduction (known mechanism; proof supplied)

Let H(m,k) count words with m copies of each letter 1,...,k that contain the subsequence 12...k. Thus H(m,k) is the (m,k) entry of OEIS A047909; A268485(n)=H(n,n), including a(0)=1. Set

W(m,k)=(mk)!/(m!)^k,  p_m(k)=H(m,k)/W(m,k).

For independent B_1,B_2,... having density m(1-b)^(m-1), 0<b<1,

p_m(k)=P(B_1+...+B_k <= 1).                                      (1)

Proof. Give every one of the mk distinguishable cards an independent uniform position in (0,1). Sorting and forgetting suits gives the uniform multiset word. Its greedy earliest realization of 12...k exists iff the word has that subsequence. Conditional on the previous successful position t, the m points for the next letter are still independent uniforms, independent of all previously revealed letters. For 0<=w<=1-t, the probability that the next letter has no point in (t,t+w] is (1-w)^m. The density of a successful next waiting time w is therefore m(1-w)^(m-1) on (0,1-t); the failure atom has mass t^m. The kernel is exactly an independent Beta(1,m) increment, killed if it exceeds 1-t, since P(B>1-t)=t^m. Success kernels and failure masses agree at every step. Induction proves (1). This does not incorrectly condition the increment on eventual success.

Equivalently N_m(1)=max{k:sum_{i<=k}B_i<=1}; its tail is p_m(k). This count is at least1 a.s. and equals the infinite-alphabet increasing-prefix length, with this convention. Some source versions use a shifted stopping index, so formulas here are fixed by (1), not a borrowed index convention.

## 2. Uniform all-orders theorem

Write h=m^(-1/2), x=(k-m)/sqrt(m), and let Phi,phi be the standard normal CDF and density. For every fixed integer R>=0 and fixed C<infinity, there are explicitly computable polynomials P_1,...,P_R such that, uniformly for integer m,k with m→infinity and |x|<=C,

p_m(k)=Phi(-x)+phi(x) sum_{j=1}^R P_j(x) m^(-j/2)
       + O_{R,C}(m^(-(R+1)/2)).                                 (2)

The first four are

P1=(x^2+8)/6,
P2=x(x^4+11x^2-6)/72,
P3=(5x^8+40x^6-561x^4-1074x^2-4848)/6480,
P4=x(5x^10-5x^8-1539x^6+3339x^4+15264x^2+173988)/155520.

### Exact finite algorithm

Let Y_m=m B. Its raw moments are

mu_r(m)=r! product_{a=1}^r (1+a/m)^(-1), mu_0=1.

Compute cumulants by

kappa_r=mu_r-sum_{a=1}^{r-1} binom(r-1,a-1) kappa_a mu_{r-a}.

For a chosen R only r<=R+2 are needed. All following series are finite Taylor expansions of these finitely many rational functions; no analyticity in h of the entire Beta moment generating function is assumed.

Use a formal variable u and form, through h^R,

E(h,u,x)=(h^(-1)+x)(kappa_1-1)u
       +[((1+xh)kappa_2-1)/2]u^2
       +(1+xh)sum_{r=3}^{R+2} h^(r-2) kappa_r u^r/r!.

Let E_j=[h^j]E and A_0=1,

A_j(u,x)=(1/j)sum_{i=1}^j i E_i(u,x) A_{j-i}(u,x).

With probabilists' Hermite polynomials He_d,

P_j(x)=-sum_{d>=1} [u^d]A_j(u,x) He_{d-1}(-x).                 (3)

The sums are finite. This algorithm is implemented independently of the exact-count checker in central_polynomials.py; derive_diagonal_fast.py uses finite polynomial arithmetic to compute diagonal coefficients through order7.

### Uniform remainder proof

Here are the analytic details needed to turn (3) into (2).

(a) Uniform moment bounds. For m>=2 the density of Y_m is

f_m(y)=(1-y/m)^(m-1) 1_{0<y<m} <= exp(-y/2).

Thus the exponential moments in a fixed complex neighborhood of zero are uniformly bounded. Since E exp(zY_m) is uniformly close to1 on a sufficiently small fixed disk, its logarithm has a single analytic branch there with uniformly bounded derivatives of each fixed order. This analyticity concerns the Fourier/mgf argument z, not the parameter h. Also Var(Y_m)=m^3/((m+1)^2(m+2))→1.

(b) Uniform small-frequency Gaussian bound. Taylor expansion of the characteristic logarithm, with the above bounds and variance bounded below, gives constants delta,c>0 such that |E exp(itY_m)|<=exp(-c t^2) for |t|<=delta and all sufficiently large m.

(c) Uniform Cramer separation. The densities f_m converge in L1 to e^(-y)1_{y>0} by dominated convergence. Hence their characteristic functions converge uniformly on the whole real line to (1-it)^(-1). On every fixed annulus delta<=|t|<=T the modulus is therefore at most a fixed q<1 for all sufficiently large m.

(d) Integrable characteristic tails. The density f_m is monotone decreasing from1 to0, with total variation1 (m>=2). Integration by parts gives |E exp(itY_m)|<=2/|t|. Choosing T>4 and combining with (c) yields

integral_{delta}^infinity |E exp(itY_m)|^k dt/t
 <= q^k log(T/delta)+(2/T)^k/k.

Thus the inversion tail beyond delta sqrt(m) for the normalized sum is exponentially small uniformly when k/m stays near1. Between a small power m^eta and delta sqrt(m), (b) makes it exponentially small in m^(2eta).

(e) Low-frequency expansion. Define T_m,k=(sum_{i=1}^k Y_{m,i}-k)/sqrt(m). Exactly,

log E exp(it T_m,k)=k[log E exp(ithY_m)-ith].

Taylor-expand this logarithm in its argument through degree R+2, using uniform derivative bounds; its remainder is O(h^(R+1)|t|^(R+3)), since k=O(h^-2). Expand only the finitely many cumulants involved in powers of h^2. The leading term is -t^2/2 and the remaining polynomial is E(h,it,x). On |t|<=m^eta with, for example, eta<1/(6(R+3)), expand its exponential through degree R. Standard finite Taylor remainders, together with the Gaussian bound, give an error bounded by

C h^(R+1) Q_R(|t|) exp(-c' t^2),

where Q_R is a fixed polynomial vanishing at0. The constants are uniform for |x|<=C. The choice of eta makes the exponent correction uniformly small on this range; all polynomial remainders are absorbed by a slightly weaker Gaussian.

(f) Fourier inversion for a CDF. Both the exact sum and the normal-polynomial approximation have continuous integrable densities once k is large. Their characteristic functions agree at0. The difference at any real threshold is bounded by the integral of their characteristic-function difference divided by |t|, up to the constant 1/(2pi). The low-frequency bound is integrable at0 because Q_R vanishes there; (b)-(d) handle the remaining ranges. Thus the CDF remainder is O(h^(R+1)), in fact uniformly in the threshold. For a term (it)^d exp(-t^2/2), its density is phi(z)He_d(z), and its integrated CDF is -phi(z)He_{d-1}(z). Evaluate at z=-x because sum B_i<=1 iff T_m,k<=-x. Formula (3) and theorem (2) follow.

## 3. Diagonal A268485

Putting x=0 gives

A268485(n) / [(n^2)!/(n!)^n]
 = 1/2 + 1/sqrt(2pi) [ 4/(3 sqrt(n))
                       -101/(135 n^(3/2))
                       +19819/(7560 n^(5/2))
                       -4463177/(272160 n^(7/2)) + ... ].        (4)

Every truncation is an asymptotic expansion with the next odd-order remainder. Specifically retaining through n^(-(2J+1)/2) gives O(n^(-(2J+3)/2)). Apply theorem (2) with R=2J+2 to obtain this bound.

Parity proof. On the diagonal, every monomial h^j u^d in E has j and d of the same parity, because each kappa_r is expanded in h^2. The property is preserved by exponentiation. Only odd d survives He_{d-1}(0). Thus only odd j contributes beyond1/2. This is a structural explanation, not a numerical guess.

Exact checks use simplex integration, an independent finite formula:

p_m(k)=m^k sum_{j_1,...,j_k=0}^{m-1}
   product_i [(-1)^(j_i) (m-1)!/(m-1-j_i)!] / (k+sum_i j_i)!.

check_renewal.py evaluates this as a power of a polynomial with integer coefficients, with a common factorial denominator. It reproduces the OEIS diagonal values 1,5,1306,46922017,449363984934526 for n=1,...,5. At n=40, sqrt(n)(p_n(n)-1/2)=0.52503197..., heading toward 4/(3sqrt(2pi))=0.53192304.... The finite checks verify formulas and signs, not the asymptotic theorem.

## 4. Inverse success thresholds and the lattice convention

For p in a fixed compact subinterval of (0,1), let z_p=Phi^(-1)(p). Define K_{m,R}(p) as the unique central real root of the R-term polynomial-normal approximation in (2) with k treated as real through x=(k-m)/sqrt(m). This is a chosen smooth approximant, not a claim that p_m(k) has a canonical real-k extension. For fixed R>=2, its asymptotic inverse begins

K_m(p)=m-z_p sqrt(m)+(z_p^2+8)/6
       +z_p(z_p^2+38)/(72 sqrt(m))+O(m^-1).                    (5)

This follows by formal implicit inversion; the derivative with respect to x of Phi(-x) is nonzero uniformly in this p-range. At arbitrary finite order the same recursion, with (2), gives a controlled smooth-root approximation.

There is no assertion that the integer threshold itself has a vanishing-error expansion. Define the exact integer threshold q_m(p)=min{k>=1:p_m(k)<=p}. Since increments are strictly positive with a density, p_m(k) is strictly decreasing. If an R-order smooth approximation K has error bounded by epsilon_m=O(m^(-R/2)), then, after enlarging the uniform error constant if needed, ceil(K-epsilon_m) <= q_m(p) <= ceil(K+epsilon_m). If this interval meets an integer boundary, exact probability evaluation is needed to determine the rounding. Away from boundaries ordinary ceiling is valid. Formula (5) by itself has smooth-root error O(m^-1).

## 5. Inverse diagonal growth

For large real n, use a finite diagonal probability expansion and gamma functions to define a smooth count carrier. Its logarithm begins

log a(n)=n^2 log n -(n/2)log(2pi n)+log n
         +(1/2)log(2pi)-1/12-log2+O(n^-1/2).

The exact factorial ratio is preferable computationally; Stirling's expansion can be continued to any finite order and combined with (4). If L=log y and

r=sqrt(2L/W_0(2L)),

then r^2 log r=L and the smooth inverse satisfies

n_*(y)=r+log(2pi r)/(4 log r+2)+O(1/r).                         (6)

In particular n_*(y)-r→1/4. Newton inversion of the finite logarithmic series supplies arbitrary further terms. Integer first-crossing indices again require bracketing rather than an unqualified rounding claim. The derivative of the leading log carrier is n(2log n+1), so any specified logarithmic error translates into the corresponding inverse error by division by that scale.

## 6. Remaining limits of the present draft

The theorem above is a central-window, all-fixed-orders expansion, with constants depending on the order and compact window. It is not a uniform large-deviation theorem, an optimally truncated transseries, or an exponential-sector theorem. Those are plausible extensions using the same exact Laplace transform, but not proved here. The source audit supports only “no higher-order central expansion located.” The leading half-factor, Gaussian transition, exact renewal law, and fixed-row leading asymptotics should not be marketed as newly open problems.
