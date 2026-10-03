# Sharp lower coefficient bound by exact-length sine-square blocks

Proof derivation, 2 October 2026. Independently reviewed; see audit/independent-audit.md. Constants and the exact positive height-walk representation are as in the frozen A202061 report.

Write L=log n, v=(2z_*^2-7z_*+2)/2, and F=n^(1/3)L^(2/3).
The aim is

limsup [n log(mu)-log a_n]/F <= C_*,
C_*=(3pi^2 alpha^2/(2v))^(1/3).

## 1. Uniform block estimate used

Only a local positive lower bound is needed; no global tail estimate or full local equivalent is assumed. The kernel note supplies the exact Hessian and optimized q saddle. For ell>=L^K, K>3, and |d|<=C sqrt(ell L), sum the binomial multiplicities B(ell,q,q+d-1) over the integer window

|q-alpha ell-beta(d-1)|<=A sqrt(ell),
beta=Sigma_qd/v.

For any sufficiently large fixed A, the result, after multiplication by rho^ell t_*^d, is bounded below by

c ell^(-2) exp[-d^2/(2v ell)-o(1)],             (1)

uniformly in these ranges. A fixed A suffices for a fixed positive fraction of the Gaussian q mass; an asymptotic equivalent for that truncated window is unnecessary. All its q satisfy |q-alpha ell|<=C' sqrt(ell L). The -1 in d-1 changes the Gaussian exponent only by o(1) uniformly here and changes its prefactor by a fixed factor t_*.

Here is a direct proof of (1) using just the positive j=q summand in the exact binomial formula. Let H_S be the Hessian of S(a,a+w,u) at (alpha,0,kappa), where S is the frozen report's factorial entropy. It is negative definite, and the w,w entry of (-H_S)^(-1) is v. At fixed s=d-1, the minimizing Gaussian choices of q-alpha ell and k-kappa ell are fixed linear functions of s. Restrict q and k to fixed-width O(sqrt(ell)) integer windows about these conditional centers. All factorial arguments remain in a compact positive interior set. Uniform Stirling gives each summand a factor at least c ell^(-3), and Taylor expansion gives the tilted exponential

exp[-s^2/(2v ell)-O(1)-O(L^(3/2)/sqrt(ell))].

There are at least c ell pairs (q,k) in these windows, giving ell^(-2). The remainder is o(1) for ell>=L^K, K>3. The conditional q center is alpha ell+beta s, as stated. This proves (1) without summing any j<q terms and without controlling the rest of the coefficient sum.

Using the exact first term x of the macro multiplier x/(1-x), each such block has total degree ell+1. Fixed multiplicative constants per block cost O(number of blocks) in the logarithm.

## 2. Deterministic heights and central lengths

Choose

M=round[(12 pi^2 alpha^2 n/(vL))^(1/3)],
J=ceil(L^3), eta=L^(-1/4),
s_j=sin^2(pi j/M), J<=j<=M-J,
S=sum_{j=J}^{M-J-1} s_j,
H0=alpha n/[(1-eta)S], h_j=floor(H0 s_j).

For sufficiently large n, J<M/4. Put m=M-2J, h0=h_J=h_{M-J}. The elementary sine estimates give

S~M/2, H0~2alpha n/M,
h0=Theta(L^7), min_j h_j=Theta(L^7),
H0/M^2=Theta(L).

Let

n'=n-m-2h0-1.

Choose positive integer central lengths ell_j with

sum ell_j=n', ell_j=(n'/S)s_j+O(1)

by rounding down and distributing the remaining fewer than m units. Set

g_j=h_{j+1}-h_j, so sum g_j=0.

Uniformly,

ell_j=(1-eta)h_j/alpha *[1-o(eta)]+O(1),
ell_j>=cL^7, |g_j|<=C sqrt(ell_j L).          (2)

The small discrepancy n'/n=1-o(eta) follows because m+h0=o(n eta).

## 3. Summed independent rectangles and exact constraints

For each j allow independently

ell=ell_j+u_j, |u_j|<=w_j=floor(ell_j/L^2),
d=g_j+v_j, |v_j|<=b_j=floor(sqrt(ell_j)).

Retain only choices satisfying the two global equalities

sum u_j=0, sum v_j=0.                         (3)

These enforce the exact prescribed total degree and exact return to h0. For each such choice, use the q window in (1).

### All these choices are legal

At the start of block j, the actual height is h_j+E_j, where E_j is the partial sum of the v_i. Using both the prefix sum and, by (3), its complementary suffix sum,

|E_j| <= min(sum_{i<j} b_i, sum_{i>=j} b_i)
       <= C h_j/sqrt(L).                    (4)

To verify the last inequality on the ascending half, use b_i<=C sqrt(n/M) sin(pi i/M), and

sum_{i=J}^{j-1} sin(pi i/M)
 <= C M [1-cos(pi j/M)] <= C M s_j.

Divide by h_j~(n/M)s_j and use M^(3/2)/sqrt(n)=Theta(L^(-1/2)). The descending half follows by the complementary suffix and symmetry. Rounding terms are smaller because the minimum h_j is Theta(L^7).

Every q in (1) obeys

q<=alpha ell_j(1+O(L^(-2)))+C sqrt(ell_j L).

The margin eta h_j dominates the right-side perturbation, (4), and all roundings: eta=L^(-1/4), whereas |E_j|/h_j=O(L^(-1/2)) and sqrt(L/h_j)=O(L^(-3)). Hence q<=h_j+E_j. All intermediate heights are positive. Thus every retained choice is an admissible height walk.

### The two constraints lose only a polynomial factor

The generating polynomial for each independent integer interval [-w_j,w_j] has symmetric unimodal coefficients. Convolution preserves symmetry and unimodality, so the number of length choices with sum u_j=0 is at least

prod_j(2w_j+1)/(2sum_j w_j+1).

The same argument applies separately to the increment choices. Therefore the number of pairs satisfying (3) is at least

prod_j[(2w_j+1)(2b_j+1)]/(2n+1)^2.           (5)

Here sum w_j<=n and sum b_j<=n for large n. The elementary convolution fact follows, for example, by expressing a symmetric unimodal sequence as a nonnegative sum of indicators of centered intervals; convolution of two such interval indicators is symmetric unimodal.

## 4. Exact seeds and all integer n

The ascent seed from height 1 to h0 has q=1,r=h0-1 and degree 2h0-1, with multiplicity at least 1. The descent seed from h0 to 1 has q=h0,r=0 and degree 1, also with multiplicity 1. Include the original leading letter of degree 1. The total seed degree is 2h0+1.

Together with the m leading x factors of the large blocks, the total degree is

2h0+1+m+sum ell_j=n

exactly, for every sufficiently large integer n. The large-block height increments sum to zero, so all height tilts cancel. The fixed seed costs O(h0)=O(L^7)=o(F); the leading-x factors and fixed block constants cost O(M)=o(F).

No monotonicity interpolation, subsequence argument, or unbounded residual repair is needed.

## 5. Evaluate the logarithmic cost

Uniformly across the rectangles,

d^2/ell <= g_j^2/ell_j+O(sqrt(L))+O(1),
log ell=log ell_j+o(1).

This follows from (2), |v_j|<=sqrt(ell_j), and |u_j|/ell_j<=L^(-2). Combining (1), (5), and w_j~ell_j/L^2, b_j~sqrt(ell_j), gives

log(a_n rho^n)
 >=-sum_j g_j^2/(2v ell_j)
   -(1/2)sum_j log ell_j
   -O(M sqrt(L)+M log L+log n+L^7).           (6)

Every term in the final O-expression is o(F).

The sine profile gives

sum_j g_j^2/ell_j
 =(1+o(1)) 4pi^2 alpha^2 n/M^2.              (7)

For completeness, rounding errors are negligible since min ell_j~L^7. Before rounding, the sum equals

(H0^2 S/n') sum_j (s_{j+1}-s_j)^2/s_j.

Taylor expansion with an absolute remainder, followed by summation (not a pointwise relative expansion at the central zero derivative), gives

sum_j (s_{j+1}-s_j)^2/s_j
 =(1+o(1)) (4pi^2/M^2)sum_j cos^2(pi j/M)
 =(1+o(1))2pi^2/M.

Insert S~M/2, H0=alpha n/[(1-eta)S], n'~n and eta->0 to get (7).

Likewise,

(1/2)sum_j log ell_j=(1+o(1))(M/3)L.          (8)

Indeed log(n'/S)=(2/3)L+O(log L), and sum_j log s_j=O(M)+o(M). The latter follows either by a Riemann sum with integrable endpoint logarithms or from prod_{j=1}^{M-1}sin(pi j/M)=M/2^(M-1), with the O(JL)=o(M) omitted endpoint terms.

Insert (7)-(8) into (6). The leading cost is

2pi^2 alpha^2 n/(vM^2)+(M/3)L.

Our choice M^3~12pi^2 alpha^2 n/(vL) makes its first term asymptotic to ML/6, so the total is asymptotic to ML/2=C_*F. Consequently

limsup [n log(mu)-log a_n]/F <= C_*.

Together with the calibration upper bound this proves the exact leading constant. Both arguments and the local kernel estimates they require are covered by the independent mathematical audit.
