# A sub-n^(3/8) logarithmic deficit for A202061

Research proof draft, 1 October 2026. Read together with operator_proof.md. This draft is being sent for independent adversarial audit before any release claim.

## Proposed theorem

Let a_n count classical 120-avoiding ascent sequences, and let mu=7.295896943239772... be the largest root of mu^3-8mu^2+5mu+1=0. There are positive constants C,N such that

mu^n exp(-C n^(1/3) log n) <= a_n <= C mu^n      (n>=N).           (T)

Consequently, for every fixed gamma>1/3,

log(a_n/mu^n)/n^gamma -> 0.

In particular an asymptotic C_0 mu^n exp(-c n^(3/8)) n^g with c>0 cannot hold. This does not determine the true subexponential scale, its constant, or a full transseries.

Everything below uses the exact positive height-walk representation proved in operator_proof.md, rather than assuming that the diagonal kernel discriminant gives a spectral radius.

## 1. A positive exact binomial formula for each jump

Write b=1-x, beta=xt/b, eta=x^2 t/b^2. The algebraic jump series Q of equation (7) can be written

Q=(z+xW)/(1-z),
W = (z/b)(1+beta)(1+W)/(1-eta(1+W)).                              (10)

This follows by direct substitution in the quadratic. Its formal solution W has zero constant term in z. Lagrange inversion gives, for j>=1,

[z^j]W = (1+beta)^j b^(-j) sum_{k>=0} C(j,k) eta^k,
C(j,k) = (1/j) binom(j+k-1,k) binom(j+k,k+1).

The factor C(j,k) is a positive integer. Thus, writing B(ell,q,r)=[x^ell t^r]Q_q(t),

B(ell,q,r)
=1_{ell=0,r=0}
 + sum_{j=1}^q sum_{k=0}^r
   C(j,k) binom(j,r-k) binom(j+ell-2,ell-r-k-1),                  (11)

where only ell>=r+k+1 and 0<=r-k<=j are included. Formula (11) is for q>=1, ell,r>=0. It has been checked independently against the gap-operator recurrence. In particular retaining just j=q and any admissible k gives the rigorous positive lower bound

B(ell,q,r)>= C(q,k) binom(q,r-k) binom(q+ell-2,ell-r-k-1).          (12)

## 2. Exact entropy point

Let alpha be the unique positive root of

7alpha^3+14alpha^2-7alpha-1=0,

and put

kappa=(-21alpha^2+17alpha+5)/29,
mu=(1+alpha)/(1-alpha-kappa),
z_*=kappa(1-alpha-kappa)/((alpha-kappa)(2alpha+kappa)).

Rational root isolation and exact polynomial reduction give

alpha=0.5100033746178888...,
kappa=0.2830305201361994...,
z_*=0.1980622641951617...,
mu=7.2958969432397724... .

In particular all of alpha, kappa, alpha-kappa, and 1-alpha-kappa are strictly positive; also kappa<alpha and alpha+kappa<1. The displayed mu is the largest root of mu^3-8mu^2+5mu+1, and z_* satisfies z_*^3-5z_*^2+6z_*-1=0. The script critical_certificate.py verifies these identities over Q[alpha] and all necessary strict inequalities using rational interval arithmetic.

Let L(v)=v log v for v>0, and define

S(a,d,k)=2L(a+k)-L(a)-2L(k)-L(d-k)-L(a-d+k)
         +L(1+a)-L(1-d-k)-L(a+d+k).

This is the entropy of the right-hand side of (12), divided by ell, at a=q/ell,d=r/ell,k=k/ell. At the point (alpha,alpha,kappa), exact algebra gives

S_k=0, S_a+S_d=0, S_d=log z_*, S=log mu.                         (13)

For completeness, the first two stationarity equations reduce to

(alpha+kappa)^2(alpha-kappa)(1-alpha-kappa)
 = kappa^3(2alpha+kappa),

(alpha+kappa)^2(1+alpha)(1-alpha-kappa)
 = alpha(alpha-kappa)(2alpha+kappa)^2.

Euler's identity for the homogeneous factorial entropy then gives

S=log((1+alpha)/(1-alpha-kappa))=log mu.

There is no unproved assertion of a global entropy maximum here; a single interior stationary point with the stated value suffices.

## 3. Uniform positive block bound

Fix any finite D>0. There exist c_D>0 and ell_D such that whenever ell>=ell_D and integers q,r,k satisfy

|q-alpha ell|<=2,
|k-kappa ell|<=1,
|r-q|<=D sqrt(ell),

all the binomial arguments in (12) are admissible, and

B(ell,q,r)>=c_D ell^(-3) mu^ell z_*^(r-q).                        (14)

Proof: all scaled factorial arguments remain in one compact subset of the positive interior. Standard uniform Stirling inequalities give a lower bound c ell^(-3) exp(ell S(q/ell,r/ell,k/ell)). The polynomial factor is explicit from

C(q,k)=q/((q+k)(k+1)) binom(q+k,k)^2

and

binom(q+ell-2,ell-r-k-1)
 = ((ell-r-k)(q+r+k))/((q+ell)(q+ell-1))
   *binom(q+ell,ell-r-k).

The four ordinary binomial factors (counting the square twice) contribute ell^(-2), and the C prefactor contributes ell^(-1). By (13), Taylor's theorem on this compact set gives

ell S = ell log mu+(r-q) log z_*+O_D(1),

because the q and k errors are bounded and r-q=O_D(sqrt ell). Absorb this bounded error into c_D. This proves (14).

The full macro-step has generating weight x/(1-x) times [t^r]Q_q(t). Retain only its leading factor x. Thus a macro-step with block length ell, down parameter q, and rise parameter r has length ell+1, multiplicity B(ell,q,r), and height increment

delta=1-q+r.

Its legality condition is exactly q<=h, with h>=1; the resulting height is h+delta>=1. No boundary condition is dropped.

## 4. Square-height ascent and descent

Choose one sufficiently large fixed integer J. All exceptions involving small ell are absorbed into this fixed choice. Define, for j>=J,

h_j=j^2,
q_j=floor(j^2/2),
ell_j=floor(q_j/alpha).

Then q_j-alpha ell_j is bounded in [0,alpha), and ell_j=Theta(j^2). Choose k_j to be a nearest integer to kappa ell_j.

An ascent step h_j -> h_{j+1} has

r_j^+=q_j+2j,

because its height increment must be 2j+1. A descent step h_j -> h_{j-1} has

r_j^-=q_j-2j,

because its increment is -2j+1. For fixed sufficiently large J, every such step satisfies (14) with the same D, because |r-q|=2j=O(sqrt ell_j), and q_j<=h_j. The final heights are positive.

Seed the walk from height 1 to height J^2 using q=1, r=J^2-1. Since

Q_1(t)=1/(1-x-x^2t/(1-x)),

its [t^r] coefficient has leading term x^(2r), with coefficient 1. The seed macro therefore has length 2J^2-1 and multiplicity at least 1. After the square-height ascent and descent, return from J^2 to 1 using q=J^2, r=0, ell=0; this has length 1 and multiplicity 1.

For K>=J, ascend through J^2,(J+1)^2,...,K^2, then descend through (K-1)^2,...,J^2. Add the seeds and the original leading letter 0. The resulting word length is

L_K=2J^2+1
 +sum_{j=J}^{K-1}(ell_j+1)+sum_{j=J+1}^{K}(ell_j+1).

Therefore

L_K=K^3/(3alpha)+O(K^2),
L_{K+1}-L_K=ell_K+ell_{K+1}+2=K^2/alpha+O(K).

There are 2(K-J) large blocks. Their total height increment is zero, so

sum(r-q)=-2(K-J).

Thus their tilt factors z_*^(r-q) cancel to one fixed factor z_*^(-1) per block, rather than leaving an exponentially expensive endpoint-height factor. The two fixed seeds cost only a fixed constant.

## 5. Every large length, not just a subsequence

Given large n, let K be maximal with L_K<=n and put R=n-L_K. Then

0<=R<ell_K+ell_{K+1}+2.

If R is bounded by a fixed sufficiently large threshold, absorb it using the terminating factor 1/(1-x), whose every coefficient is 1. This loses only a fixed factor in comparison to mu^n.

Otherwise split R=m_1+m_2 into two nearly equal integers, each above that fixed threshold, and insert two self-loops at height K^2. For a loop of length m set

ell=m-1,
q=nearest integer to alpha ell,
r=q-1,
k=nearest integer to kappa ell.

Its height increment is zero and (14) applies. Moreover

q<=alpha R/2+O(1)<=K^2/2+O(K)<K^2

for large K, so both loops are legal. The two loop lengths absorb R exactly. All word lengths are therefore covered.

Combining (14) over O(K) blocks, with ell<=O(K^2), yields

log a_n >= n log mu-O(K)-3 sum log ell-O(1)
          >= n log mu-O(K log K)
          >= n log mu-O(n^(1/3) log n).

This proves the lower half of (T). The height-walk identities are coefficientwise equalities to the original word class, and all selected block coefficients are positive; multiplying the selected factors consequently gives a legitimate coefficient lower bound. An additional explicit natural word-level bijection is not assumed.

## 6. Direct finite upper bound at the critical point

This part independently controls the exponential rate; it does not require the A202062 result. Put rho=1/mu, b=1-rho, t_*=1/z_*, beta_*=rho/(b z_*), eta_*=rho^2/(b^2 z_*), and

Q_*=b z_*/(b z_*+rho),
W_*=((1-z_*)Q_*-z_*)/rho.

The exact certificate verifies the fixed-point identity (10) at (rho,z_*,t_*,W_*), and verifies

W_*>0, 0<eta_*(1+W_*)<1.

Because the right side of (10), expanded geometrically in eta, has nonnegative coefficients, iteration from W=0 is bounded by W_*. Its least formal solution therefore converges at this point, and

Q(rho;z_*,t_*)<=Q_*.

The total tilted macro mass is at most

m_*=(rho/b)t_* Q_*=rho/(b z_*+rho)
   =0.4450418679...<1.

For the weighted norm with height weight t_*^h, the unrestricted q,r sum majorizes every legal row and has norm at most m_*. The terminating weight 1/b is at most t_*^h/b for h>=1. Hence the nonnegative Neumann series defining e_h satisfies

e_h(rho)<=t_*^h/(b(1-m_*)).

Thus

A202061(rho)=1+rho e_1(rho)
 <=1+rho t_*/(b(1-m_*))<infinity.

The displayed algebraic upper bound is about 2.4450418679. Nonnegative coefficients give a_n<=A202061(rho) rho^(-n), completing (T).

## Reproducible checks

- critical_certificate.py: exact critical-point identities and rational interval inequalities
- block_formula.py: exact positive formula versus the gap operators
- check_operators.py: 1,617 independent normalized-state/operator coefficient comparisons
- check_height_walk.py: positive binomial-weight height walks, original state recurrence, and OEIS agree through n=20

These finite checks are diagnostics; the theorem rests on the displayed operator proof, positive coefficient formula, elementary uniform Stirling bound, and all-length staircase construction.
