# Full asymptotics for partition sums of acyclic orientations

Research proof, 1 October 2026. Prepared for independent mathematical review.

## 1 Main statement and scope

Write B_+(n)=A372395(n) and B_-(n)=A370613(n). They sum AO(K_lambda) over integer partitions of n, unrestricted for + and with distinct parts for -. The primary prior result is Sun, arXiv:2605.04006v1, Theorem 11: log(B_eta(n)/n!) ~ C_eta sqrt(n). Section 11 explicitly asks for the prefactor and complete expansion. The present argument supplies that refinement. It does not claim a new proof of the logarithmic constant as its main result.

For eta in {+1,-1}, put

    rho_eta(x;c) = 1/(exp(c*x+x^2/2)-eta),
    J_eta(c) = -eta * integral_0^infinity log(1-eta*exp(-c*x-x^2/2)) dx,
    M_j(c) = integral_0^infinity x^j rho_eta(x;c) dx.

Choose c=c_eta by M_1(c)=1. For eta=+1 there is one solution c>0; for eta=-1 there is one real solution. Set

    C=c+J(c),
    V=J''(c)=integral x^2 rho(1+eta*rho) dx,
    E=exp(1/2-M_3/3+M_2^2/8),
    p_+=1,                 A_+=sqrt(c)*E/(2*pi*sqrt(V)),
    p_-=3/4,               A_-=E/(2*sqrt(pi*V)).

Then, for every fixed integer L>=0,

    B_eta(n) = A_eta n! n^(-p_eta) exp(C_eta sqrt(n))
               * (sum_{j=0}^L a_{eta,j} n^(-j/2) + O_L(n^(-(L+1)/2))),
    a_{eta,0}=1.

Section 7 below gives an arbitrary-order finite coefficient algorithm. Numerically,

    c_+ =  0.76499644227954430192392445865356066525...
    C_+ =  2.15875200565778553173735731440478257232...
    A_+ =  0.16481752396442050396187672134838365615...
    a_+,1 = -0.30756533355163369663854197121934666309...
    a_+,2 =  0.01872663225856492421076350893326907627...

    c_- = -0.32369731409503187161095918076365289101...
    C_- =  0.90572982172019901788916250016056881568...
    A_- =  0.21799921291820252233936031170847439859...
    a_-,1 = 0.23095021320861498101957980466695660800...
    a_-,2 = -0.00424706612039284283055321876544848693...

All integrals in this document without displayed limits run over (0,infinity). All expansions are finite-order Poincare expansions; no convergent infinite inverse-power series or exponentially complete transseries is asserted.

## 2 Exact finite representations

Let S(k,j) denote the second-kind Stirling number and define

    P_k(t)=sum_{j=0}^k (-1)^(k-j) S(k,j)t^j,
    R_k(t)=P_k(t)/t^k.

The exponential generating function is exp(t*(1-exp(-z))). A proper coloring of a complete multipartite graph partitions each independent part into monochromatic blocks; colors used in different parts must differ. Evaluating the chromatic polynomial at -1 and applying Stanley's acyclic-orientation identity gives

    AO(K_lambda)=integral_0^infinity exp(-t) product_i P_{lambda_i}(t) dt.

This identity is exact, but its integrand can have either sign. Infinite product-integral expressions are only coefficientwise formal. Every argument below first truncates the allowed part size, so all coefficients are finite sums of polynomials.

For T~Gamma(n+1,1) and K a positive integer, define

    F_{eta,K}(q,t)= product_{k=1}^K (1-eta*q^k R_k(t))^(-eta).

The normalized sum restricted to max(lambda)<=K equals

    B_{eta,K}(n)/n! = E_T [q^n] F_{eta,K}(q,T).

To verify, extract q^n first. Every profile has total size n, so all factors t^k removed from P_k contribute exactly t^n, which combines with exp(-t)/n! into the Gamma density. This is a finite identity and involves no unsigned-measure assumption about P_k.

## 3 Root control and a uniform quadratic majorant

The recurrence

    P_{k+1}(t)=t*(P_k(t)-P'_k(t)),  P_1(t)=t,

proves by interlacing that P_k has k distinct nonnegative real roots, including 0. Indeed P_k-P'_k has one root in every gap between consecutive roots of P_k and one to the right of its largest root: signs at consecutive roots alternate, and its sign at the largest root is negative while its leading coefficient is positive. These k roots are positive; multiplying by t gives the next polynomial.

Let p_r(k) be the r-th power sum of these roots. With formal variable u,

    log(product_i(1-r_i u))=-sum_{r>=1} p_r(k)u^r/r,

and the recurrence implies

    p_r(k+1)-p_r(k)
      = -r [u^r] log(1-k*u-sum_{j>=1}p_j(k)u^(j+1)),  p_r(0)=0.       (R)

For fixed r, only j<r is needed. Induction shows p_r(k) is a polynomial of degree at most r+1: every monomial contributing to [u^r] has degree at most r in k, and summation in k raises degree by at most one. The first relevant values are

    p_1(k)=k(k-1)/2,
    p_2(k)=k(k-1)(4k-5)/6,
    p_3(k)=k(k-1)(9k^2-25k+18)/8,
    p_4(k)=k(k-1)(64k^3-291k^2+459k-251)/30.

Consequently the largest root is at most p_4(k)^(1/4)=O(k^(5/4)). Fix beta strictly between 3/4 and 4/5, for example 31/40. If every part is <=n^beta, every root of every factor is o(n). Thus P_k(t)>0 for t in [n/2,2n], uniformly over these profiles.

For a partition lambda of n set

    Q=sum_i lambda_i^2, A=(Q-n)/2,
    B=sum_i lambda_i(lambda_i-1)(4lambda_i-5)/12.

On [n/2,2n], the exact inequality log(1-v)<=-v-v^2/2 gives

    product_i P_{lambda_i}(t) <= t^n exp(-A/t-B/t^2).

Weighted Cauchy--Schwarz and a termwise comparison give

    A^2/n <= sum_i lambda_i(lambda_i-1)^2/4 <= B,

because the difference in the second inequality for one part k is k(k-1)(k-2)/12.

Put x=t/n, a=A/n^2 and g(x)=log(x)-x+1. Relative to n^n exp(-n-A/n), the integrand is at most

    exp(n*(g(x)+a*(1-1/x)-a^2/x^2)).

For x<=1 the a terms are nonpositive. For x>=1 their supremum over a>=0 is (x-1)^2/4. There is an absolute delta>0 such that

    g(x)+(x-1)^2/4 <= -delta*(x-1)^2,  1/2<=x<=2.

For example the left side vanishes only at 1: its derivative is (x-1)*(1/2-1/x), and its value at 2 is log(2)-3/4<0. The ratio by (x-1)^2 extends continuously at 1 with value -1/4. Integrating yields an absolute constant C0 with

    integral_{n/2}^{2n} exp(-t) product_i P_{lambda_i}(t) dt
      <= C0 n! exp(-(Q-n)/(2n)).                                   (M)

This proof also gives the same bound with an extra factor exp(-delta*z^2) pointwise, where z=(t-n)/sqrt(n), up to the common Stirling/Gamma normalization.

The signed tails are harmless. A permutation cycle partition maps onto a set partition, so unsigned first-kind Stirling coefficients dominate the second-kind coefficients. Hence for t>=0 and k<=M,

    |P_k(t)| <= sum_j S(k,j)t^j <= t(t+1)...(t+k-1) <= (t+M)^k.

For M<=n^beta=o(n), the tails outside [n/2,2n] are bounded by

    integral_outside exp(-t)(t+M)^n dt = n! exp(-Omega(n)+O(M)).

This follows by substituting t+M and the elementary Gamma Chernoff bounds. Since A/n<=M/2, this is negligible compared with n! exp(-A/n), uniformly. Positivity of AO and the triangle inequality now prove the uniform majorant

    AO(K_lambda)/n! <= C1 exp(-(Q-n)/(2n)),  max(lambda)<=n^beta.       (QM)

## 4 Removing large parts and Gamma tails at relative precision

Take s=sqrt(n) and K=floor(s*log(n)). First consider K<max(lambda)<=n^beta. The majorant (QM) reduces this part of the sum, apart from a constant exp(1/2), to the positive weighted partition model with weights w_k=exp(-k^2/(2n)). At q0=exp(-c/s), its product is

    F_eta(q0)=product_{k>=1}(1-eta*w_k*q0^k)^(-eta).

For unrestricted partitions c>0 and all geometric ratios are <1. For distinct partitions factors may have w_k*q0^k>1, but remain finite and positive and correspond to Bernoulli variables. A union bound gives the weighted coefficient containing a part>K at most

    q0^(-n) F_eta(q0) sum_{k>K} w_k*q0^k/(1-w_k*q0^k)   (eta=+1),

or the same expression with denominator 1 when eta=-1. The sum is exp(-Omega(log^2 n)) times a fixed polynomial in n. Euler--Maclaurin, as detailed in Section 5, gives

    q0^(-n)F_eta(q0)=exp(C*s+O(log n)).

Therefore this tail is exp(C*s) times a quantity smaller than every inverse power of n.

For max(lambda)=L>n^beta, split all other parts into singletons. Edge monotonicity of AO gives

    AO(K_lambda) <= AO(K_{L,1,...,1})=(n-L)!*(n-L+1)^L.

The last formula follows by ordering the singleton vertices and assigning the L labeled vertices to their n-L+1 gaps. Moreover

    (n-L)!*(n-L+1)^L/n!
      = product_{j=1}^L (1+(j-1)/(n-L+1))^(-1)
      <= exp(-L(L-1)/(2n)).

Here log(1+x)>=x/(1+x), and n-L+j<=n. Since 2beta-1>1/2, multiplying by the elementary partition bound p(n)<=exp(O(sqrt(n))) leaves an exponentially negligible contribution. This establishes cutoff removal at any relative algebraic order once the main coefficient is shown to have scale exp(C*s) times a fixed power of n.

For max(lambda)<=K the Gamma restriction |T-n|<=s*log^2(n) also costs less than every inverse power of n on that scale. On [n/2,2n] use the pointwise exp(-delta*z^2) bound from the proof of (M), then sum the weights exp(-(Q-n)/(2n)); outside [n/2,2n] use the signed absolute-tail bound. This avoids treating the Gamma integrand as a globally positive measure.

## 5 The local product expansion

Put epsilon=1/s and T=s^2+s*z. Uniformly for |z|<=log^2(n) and k<=K, expand the exact root product:

    log R_k(T)=-sum_{r>=1} p_r(k)/(r*T^r).

This admits controlled arbitrary finite truncation. If r_max is the largest root, the remainder after r=R is bounded in absolute value by

    p_{R+1}(k)/((R+1)*T^(R+1)*(1-r_max/T)).

Here r_max/T=o(1), uniformly, and p_{R+1}(k)=O_R((1+k)^(R+2)). It follows that termwise formal expansion in epsilon, with x=k*epsilon, yields polynomials ell_j(x,z):

    log R_k(s^2+s*z) = -x^2/2 + sum_{j>=1} epsilon^j ell_j(x,z).

Every ell_j vanishes at x=0. The first two are

    ell_1=x/2+z*x^2/2-x^3/3,
    ell_2=-z*x/2-z^2*x^2/2+2*z*x^3/3+3*x^2/4-3*x^4/8.

Define formal coefficient functions f_j by

    -eta log(1-eta exp(-c*x-x^2/2+sum_{j>=1}epsilon^j ell_j(x,z)))
        = f_0(x;c)+sum_{j>=1}epsilon^j f_j(x;c,z).                  (F)

For j>=1, each f_j is smooth at x=0. In the Bose case this follows because the m-th derivative of the outer logarithm has a pole of order at most m at 0, while every product of m ell-factors vanishes to at least order m. At infinity these functions and their derivatives decay as a Gaussian times a polynomial. These facts justify ordinary Euler--Maclaurin to arbitrary finite order, uniformly for c in a sufficiently small complex neighborhood of its real saddle and with polynomial bounds in z.

For the Fermi case, f_0 is smooth at zero and f_0(0)=log(2). For the Bose case, remove the sole logarithmic singularity by subtracting f_std(x)=-log(1-exp(-c*x)). The difference

    d_0(x;c)=f_0(x;c)-f_std(x;c)

is smooth with d_0(0)=0. The elementary eta-product expansion gives

    sum_{k>=1} f_std(k*epsilon)
      = pi^2/(6*c*epsilon)+(1/2)log(c*epsilon/(2*pi))-c*epsilon/24
        +O(exp(-b/epsilon)),

uniformly in the same small complex neighborhood. Alternatively, its finite-order version follows from Mellin inversion of Gamma(v)zeta(v)zeta(v+1), moving the line past finitely many poles; this suffices here and avoids requiring an exponentially small error.

Consequently the truncated exact product, after replacing its superpolynomially small k>K tails in the coefficient functions, has expansion

    log F_{eta,K}(exp(-c*epsilon),T)
      = J(c)/epsilon + r_eta log(epsilon)+d_eta(c)
        +sum_{j>=0}epsilon^j H_j(c,z),                            (P)

where

    r_+=1/2, d_+(c)=(1/2)log(c/(2*pi)),
    r_-=0,   d_-(c)=-(1/2)log(2),
    H_0=M_1/2+z*M_2/2-M_3/3.

An explicit algorithm for j>=1 is

    H_j = integral f_{j+1}(x) dx - f_j(0)/2
           - sum_{m=1}^{floor(j/2)} B_{2m}/(2m)! * f_{j-2m+1}^{(2m-1)}(0)
           + E_j(c).                                           (EM)

For eta=-1, E_j=0 when j is even and E_j=-B_{j+1}f_0^(j)(0)/(j+1)! when j is odd. For eta=+1, E_even=0,

    E_1=-c/24 - B_2*d_0'(0)/2! = (1/c-c)/24,
    E_j=-B_{j+1}d_0^(j)(0)/(j+1)! for odd j>=3.

Only finitely many root power-sum polynomials and derivatives are required for any specified H_j. For example, with K_j=integral x^j rho(1+eta*rho) dx,

    H_1(z) = e +3*M_2/4-3*M_4/8+K_2/8-K_4/6+K_6/18
      +z*(-M_1/2+2*M_3/3+K_3/4-K_5/6)
      +z^2*(-M_2/2+K_4/8),

where e=-c/24-5/(24*c) for Bose and e=c/24 for Fermi.

## 6 Fourier localization and the leading amplitude

For fixed central T, the product coefficients are nonnegative. On q=q0*exp(i*theta), the ratio of absolute product value to its value at q0 is a characteristic-function modulus. Choose a fixed interval of integers a*s<=k<=b*s with 0<a<b. For these factors the corresponding geometric or Bernoulli parameters remain in a compact nondegenerate interval, uniformly for central z. Therefore

    |F(q0*exp(i*theta),T)|/F(q0,T)
      <= exp(-d sum_{a*s<=k<=b*s}(1-cos(k*theta)))
      <= exp(-d' min(s^3*theta^2,s)),   -pi<=theta<=pi.             (A)

For |theta|<=c0/s the second inequality follows from 1-cos(k*theta)>=const*k^2*theta^2. For theta between c0/s and C0/s it follows by compactness from the limiting nonzero integral of 1-cos(x*v). For |theta|>=C0/s, the geometric-sum bound on sum exp(i*k*theta), with C0 sufficiently large, gives a positive fraction of the interval length. These cover the full circle and establish the bound without a lattice-periodicity assumption left implicit.

Thus only |theta|<=s^(-3/2)log^2(n) matters at any algebraic order. Set theta=u*s^(-3/2). In the product expansion replace c by

    c'=c-i*u/sqrt(s)=c-i*u*sqrt(epsilon).

The factor q^(-n) cancels the first derivative of J precisely because J'(c)=-M_1(c)=-1. The quadratic exponent is -V*u^2/2. The exact Gamma density of z is

    (2*pi)^(-1/2) exp(-z^2/2)
       * exp(sum_{j>=1}(-1)^(j+1)epsilon^j z^(j+2)/(j+2)
              -sum_{m>=1} B_{2m}epsilon^(4m-2)/(2m*(2m-1))).       (G)

This is an arbitrary finite Stirling/Taylor expansion with its usual uniform remainder on the central window. The constant z-dependent amplitude from (P) is

    exp(H_0)=exp(1/2-M_3/3)*exp(z*M_2/2).

The Gaussian z integral therefore contributes exp(1/2-M_3/3+M_2^2/8). The Fourier integral contributes 1/sqrt(2*pi*s^3*V). The boundary factor is sqrt(c/(2*pi*s)) for Bose and 1/sqrt(2) for Fermi. Multiplying proves exactly the amplitudes and powers stated in Section 1.

## 7 A finite algorithm at every order

Let U and Z be independent real Gaussian variables,

    U~N(0,1/V),       Z~N(alpha,1),       alpha=M_2/2.

Treat epsilon^(1/2) as a formal variable and put delta=-i*U*sqrt(epsilon). Define

    Q(epsilon,U,Z) =
      sum_{r>=3} J^(r)(c)*(-i*U)^r*epsilon^(r/2-1)/r!
      +d(c+delta)-d(c)
      +H_0(c+delta,Z)-H_0(c,Z)
      +sum_{j>=1}epsilon^j H_j(c+delta,Z)
      +sum_{j>=1}(-1)^(j+1)epsilon^j Z^(j+2)/(j+2)
      -sum_{m>=1} B_{2m}epsilon^(4m-2)/(2m*(2m-1)).

Then

    a_j = [epsilon^j] E exp(Q(epsilon,U,Z)).                      (C)

At each prescribed order this is finite algebra: compute (R), (F), (EM), Taylor-expand in delta, and use Gaussian moments. Odd half-integer powers vanish because their integrands are odd in U. In particular all a_j are real and the expansion has powers n^(-1/2), with no additional logarithms.

For a directly checkable first correction, write A0(c,z)=exp(d(c)+H_0(c,z)). The Fourier part at order epsilon is

    D(z) = -A0_cc/(2*V*A0)+J'''*A0_c/(2*V^2*A0)
             +J''''/(8*V^2)-5*(J''')^2/(24*V^3).

Thus

    a_1=E_{Z~N(alpha,1)} [H_1(c,Z)+Z^3/3+D(Z)].                  (C1)

The supplied first_correction.py evaluates this using only one-dimensional rapidly convergent integrals.

### Error control for the arbitrary-order algorithm

Here are the necessary uniformity details. The largest-part and Gamma cutoffs were justified at relative precision independently in Sections 3--4. The Fourier tails satisfy (A) uniformly in the remaining Gamma window. In the local integral, all root-product Taylor remainders are controlled by the displayed positive-root bound. One can expand finitely many extra orders to obtain any target power of epsilon. Derivatives of f_j are integrable in x, have at most polynomial dependence on z, and are uniform for c in a fixed complex neighborhood. The Bose singular part was removed exactly, so its Euler--Maclaurin remainder has the same property. Euler--Maclaurin remainder bounds follow from the integral of the relevant derivative; these integrals are bounded by a fixed polynomial in |z|.

For clarity, the profilewise majorant alone cannot bound the two-variable product integrand: the product F(q0,T) also sums profiles of sizes other than n. The needed joint Gaussian envelope follows directly from the first-order local product estimate. Namely, retaining ell_1 and bounding the next Taylor remainder by its integrable derivatives gives, uniformly for |z|<=log^2(n),

    log F(q0,T)=s*J+r_eta*log(epsilon)+d_eta+H_0(c,z)
                  +O(epsilon*(1+z^2)).

To verify this bound, log R_k+x^2/2=epsilon*ell_1+O(epsilon^2*(1+z^2)*P(x)) on the cutoff range for a fixed polynomial P with P(0)=0; this endpoint factor follows because all root power-sum polynomials vanish at k=0. The linear outer-log derivative times P and the quadratic remainder times ell_1^2 are integrable, including at the Bose endpoint because P=O(x) and ell_1=O(x). Summing over the mesh multiplies the error by s. Euler--Maclaurin boundary remainders have the same bound. The Gaussian decay in x makes the polynomial integrable and removes any dependence on the growing k cutoff.

Since H_0 is affine in z, the exact Gamma density times F(q0,T), after division by the common exp(C*s) and boundary factors, is bounded by

    C2*exp(-z^2/2+alpha*z+O(epsilon*(1+|z|^3)))
        <= C3*exp(-z^2/4)

for all sufficiently large n on this window. The cubic Gamma error is absorbed because epsilon*log^2(n)->0. Combining this real-axis bound with (A) yields a joint Gaussian envelope in u and z.

After the Fourier Taylor expansion, remainders are therefore bounded by a fixed polynomial in |u|+|z| times the target epsilon power, multiplied by exp(-d2*u^2-d3*z^2), after possibly reducing the positive constants. Integrating these polynomials against the envelopes gives finite constants independent of n. This prevents logarithmic cutoff powers from contaminating the final O(epsilon^(L+1)) error. Expand through the next odd half-power before integrating; its exact oddness cancels, leaving the stated integer-power remainder. Every operation in (C) is consequently justified at any fixed order, and cutoff removal proves Section 1 for the original full sums.

## 8 Smooth inverses and integer thresholds

Let b_j be the formal logarithm coefficients

    log(1+sum_{j>=1}a_j x^(-j/2))=sum_{j>=1}b_j x^(-j/2).

Choose a smooth realization G(x) of the logarithmic all-order expansion, with termwise differentiable asymptotics. Such a realization can be constructed using a fixed smooth cutoff and sufficiently rapidly growing cutoff radii for successive asymptotic terms; choose the radii inductively so each new term and each of its first finitely many derivatives are smaller than the required earlier remainder bounds. If exact interpolation is desired, fix a smooth bump phi supported in (-1/3,1/3) with phi(0)=1 and set

    log F(x)=G(x)+sum_{large integers m}(log B(m)-G(m))*phi(x-m).

The supports are disjoint. The correction coefficients and all their bump derivatives are flat to every algebraic order by Section 1. Therefore F(m)=B(m), F is positive, and all logarithmic derivative asymptotics are preserved. In particular F is strictly increasing eventually because (log F)'=log x+O(x^(-1/2)). This specifies the class of smooth realizations; their inverse expansions agree to every displayed algebraic order. No canonical analytic continuation of the discrete sequence is claimed.

The log expansion is

    log F(x)=x(log x-1)+C sqrt(x)+alpha0 log x+d0
              +sum_{j>=1}beta_j x^(-j/2),
    alpha0=1/2-p, d0=log(A sqrt(2*pi)).

Here beta_j combines b_j with the Stirling series; for example beta_1=a_1 and beta_2=b_2+1/12. Given L=log Y, define

    N=L/W(L/e),    ell=log N,

with the positive real Lambert W branch. Formal substitution into the log equation determines uniquely an inverse of the form

    F^(-1)(Y)=N+sum_{j>=-1}N^(-j/2) r_j(1/ell),

where the r_j are finite polynomials in 1/ell (depending on C,alpha0,d0,beta's). At each new order, the unknown coefficient enters multiplied by ell, so it is determined by division by ell. The first terms are

    N-C*sqrt(N)/ell-alpha0-d0/ell
      +C^2/(2*ell^2)-C^2/(2*ell^3)+O(1/(sqrt(N)*ell)).             (I)

To make arbitrary truncations quantitative, substitute an inverse truncation X into the log expansion, compute its residual R=log F(X)-L to one additional order, and use the mean-value theorem with (log F)'(x)~log N. A residual O(N^(-r/2)) gives inverse error O(N^(-r/2)/log N); all constants are uniform for sufficiently large Y. This is a controlled recursive inverse, rather than inversion of the leading equivalent alone.

For the integer threshold tau(Y)=min{n:B(n)>=Y}, eventual monotonicity follows from Section 1. With an increasing exact interpolant, tau(Y)=ceil(F^(-1)(Y)) for all sufficiently large Y. An asymptotic approximation X(Y) with a proven inverse error e(Y) only yields the envelope

    ceil(X(Y)-e(Y)) <= tau(Y) <= ceil(X(Y)+e(Y)).

It gives a unique integer when the two endpoints coincide; unconditional rounding of a finite asymptotic approximation is not asserted.

## 9 Reproducible checks and remaining review

exact_check.py computes exact values using positive Touchard polynomials and Kronecker substitution before the final alternating factorial evaluation. The bound p(n)Bell(n)<=2^n n^n ensures that the chosen binary digit base prevents carries. Separate runs through n=150 and n=300 agree on their full overlap, and both sequences match all 21 initial OEIS values checked. first_correction.py evaluates formula (C1); generic_second_correction.py independently expands the formal generator and reproduces both a_1 values and the displayed a_2 values. After subtracting 1+a_1/sqrt(n)+a_2/n, the n^(3/2)-scaled residual at n=300 is approximately -0.00553406 for the unrestricted sequence and +0.04126194 for the distinct sequence. These tests support the proof but are not used to establish it. validate_results.py reproduces the comparisons and checks the inverse error scales. Independent review of the complete analytical argument is recorded separately.

Sources:

- OEIS A372395, https://oeis.org/A372395
- OEIS A370613, https://oeis.org/A370613
- Zhiyang Sun, *Saddle-Point Asymptotics for Chromatic and Tutte Polynomial Evaluations of Complete Multipartite Graphs*, arXiv:2605.04006v1, https://arxiv.org/html/2605.04006v1
- Richard P. Stanley, *Acyclic orientations of graphs*, Discrete Mathematics 5 (1973), 171--178, https://doi.org/10.1016/0012-365X(73)90108-8

The exact Gamma representation and the previously known logarithmic constants are credited to Sun; the new ingredients proposed here are the relative-precision quadratic majorant, full amplitudes, all-order coefficient construction, and controlled inverse.
