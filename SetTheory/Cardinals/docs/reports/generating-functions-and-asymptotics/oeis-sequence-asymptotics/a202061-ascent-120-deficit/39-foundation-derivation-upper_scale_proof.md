# Complementary upper bound: the stretch power is 1/3 on a logarithmic scale

Research proof draft, 1 October 2026. Independent audit is required. This strengthens the upper half of stretch_bound_proof.md, using the same exact positive height-walk representation.

## Claim

There are positive constants c,C,N such that

a_n <= C mu^n exp(-c n^(1/3))     (n>=N).                         (U)

Together with the previously drafted lower bound, this yields

c n^(1/3)-O(1) <= n log(mu)-log(a_n) <= C n^(1/3) log n,

and consequently

log(n log(mu)-log(a_n))/log n -> 1/3.                             (S)

Statement (S) determines the stretch power in this precise logarithmic sense. It does not assert a pure exp(-k n^(1/3)) equivalent, a leading constant, or an all-orders expansion.

Throughout let rho,z_*,t_*,Q_*,W_*,m_* be the exact constants in stretch_bound_proof.md. In particular t_*=1/z_*>1 and m_*<1. Let c(x)=x/(1-x). A macro-step has length-generating weight c(x)[t^r]Q_q(x,t), moves h to h+1-q+r, and requires 1<=q<=h.

## 1. A uniform degree bound for fixed-gap jump weights

At fixed positive t=t_*, write b=1-x, beta=xt_*/b, eta=x^2t_*/b^2. From equation (10),

Q_q(x,t_*)=1+x sum_{j=1}^q W_j(x),

W_j(x)=((1+beta)/b)^j N_{j-1}(eta)/(1-eta)^(2j-1),               (15)

where N_0=N_1=1 and, for j>=2,

N_{j-1}(v)=sum_{l=0}^{j-2} [binom(j-1,l)binom(j-1,l+1)/(j-1)] v^l.

Formula (15) follows from the exact identity

sum_{k>=0} C(j,k)v^k
 = (1-v)^(1-2j) * {}_2F_1(2-j,1-j;2;v),

or the elementary Euler transformation of the two hypergeometric binomial series. For j>=2 the final series is exactly the displayed positive polynomial; j=1 gives (1-v)^(-1).

Choose a small fixed epsilon_0>0 such that x in [rho,rho+epsilon_0] keeps b>0 and 0<eta<1. Such an interval exists because eta(rho)=0.12737466... . The polynomial N has nonnegative coefficients and degree at most max(j-2,0). Thus

0 <= eta N'(eta)/N(eta) <= max(j-2,0)<=j,

and logarithmic differentiation of (15) gives a uniform constant C_0 with

0 <= (d/dx) log W_j(x) <= C_0 j.

It follows, enlarging a constant C_1, that

Q_q(x,t_*) <= Q_q(rho,t_*) exp(C_1(q+1)(x-rho))                  (16)

for all q>=1 and all x in this fixed interval. No large-q asymptotic is used.

## 2. Paths confined below height H

Let e_h^[H] count height walks whose every visited height is in {1,...,H}. Put

x_H=rho+epsilon/(H+1)

with a sufficiently small fixed epsilon>0. The weighted row sum at height h, using height weight t_*^h, is at most

c(x_H)t_* sum_{q=1}^H Q_q(x_H,t_*)z_*^q
 <= [c(x_H)/c(rho)] exp(C_1(H+1)(x_H-rho)) m_*.

Because m_*<1, choose epsilon so this bound is uniformly at most some m_bar<1. For all H it also lies in the interval of (16), after making epsilon small enough. The terminating weight is 1/(1-x_H), bounded uniformly. The positive Neumann series therefore gives

e_1^[H](x_H)<=C_2

with C_2 independent of H. Hence the coefficients counting words whose macro-height stays at most H satisfy

a_n^[<=H] <= C_3 x_H^(-n)
            <=C_3 mu^n exp(-c_1 n/(H+1)).                       (17)

## 3. A quadratic-cost change of height tilt

For fixed W=W_*, define the positive fixed-point map

F(x,z,t;W)=(z/(1-x))*(1+xt/(1-x))*(1+W)
          /(1-x^2 t(1+W)/(1-x)^2).

At the critical parameters F(rho,z_*,t_*;W_*)=W_*. Put

f(x,theta)=F(x,z_* exp(-theta),t_* exp(theta);W_*).

The exact identities

W_*=1+beta_*,
eta_*(2+beta_*)^2=1

imply f_theta(rho,0)=0. Indeed, with u=eta_*(1+W_*), logarithmic differentiation gives

f_theta/f = -1/(1+beta_*)+u/(1-u)=0.

Also f_x(rho,0)>0: all positive factors in F increase with x, and the denominator remains positive. Choose a large fixed D>0, and define

x_theta=rho exp(-D theta^2),
t_theta=t_* exp(theta),
z_theta=1/t_theta.

Taylor's theorem gives

f(x_theta,theta)=W_*+
 [f_{theta theta}(rho,0)/2-rho D f_x(rho,0)]theta^2+O(theta^3).

Choose D to make the bracket strictly negative. For 0<=theta<=theta_0 with theta_0 sufficiently small, F at W_* is therefore at most W_* and its denominator is positive. Positive iteration from zero proves convergence of the jump series and gives

Q(x_theta;z_theta,t_theta)
 <= (z_theta+x_theta W_*)/(1-z_theta).

The resulting unrestricted tilted row sum

m_theta=c(x_theta)t_theta Q(x_theta;z_theta,t_theta)

is bounded above by a continuous expression tending to m_*<1 as theta->0. By further reducing theta_0, it is uniformly at most another fixed m_bar<1. Consequently the sum of weights of all finite macro-prefixes, including their terminal factor t_theta^h but not a terminating 1/(1-x) weight, is uniformly bounded: it is at most

t_theta sum_{k>=0}m_bar^k <= C_4.                                (18)

This argument is a positive fixed-point supersolution. It does not assume a guessed analytic continuation or choose a square-root branch without justification.

## 4. Paths that reach height above H

Classify these by their first macro-boundary reaching height h>H. Let p_{m,h} be the total multiplicity of first-hit prefixes of length m ending there, starting from height 1. The remaining suffix has generating function e_h. The critical-point bound from stretch_bound_proof.md gives

e_h(rho)<=C_5 t_*^h.

The initial leading letter 0 contributes rho. Therefore, at any fixed word length n,

a_n^[>H] rho^n
 <=C_5 rho sum_{m<=n-1,h>H} p_{m,h}rho^m t_*^h.

For 0<theta<=theta_0,

rho^m <= x_theta^m exp(D theta^2 n),
t_*^h <= t_theta^h exp(-theta H).

The remaining sum is bounded by (18), since first-hit prefixes are a subset of all prefixes. Thus

a_n^[>H] <= C_6 mu^n exp(D theta^2 n-theta H).

For H/(2Dn)<=theta_0, choose theta=H/(2Dn). This yields

a_n^[>H] <= C_6 mu^n exp(-H^2/(4Dn)).                            (19)

The continuation at the critical tilt is essential: it cancels the potentially expensive endpoint-height factor. No assumption about the final height is imposed.

## 5. Optimization

Take H=floor(n^(2/3)). The condition for (19) holds for all sufficiently large n. Both (17) and (19) are then bounded by C mu^n exp(-c n^(1/3)). Their sum proves (U), and combining with the lower bound proves (S).

## Certificate additions

The two exact tilt identities can be checked by reducing rational functions modulo 7alpha^3+14alpha^2-7alpha-1. Their numerical values are W_*=1.8019377358... and eta_*(2+beta_*)^2=1 exactly. The polynomial fixed-gap identity can be verified independently for any prescribed q; its general proof is the displayed finite hypergeometric transformation.

### Self-contained proof of the finite Narayana transformation

Let F_j(v)=sum_{k>=0} C(j,k)v^k. The explicit factorial expression gives

(k+1)(k+2)C(j,k+1)=(k+j)(k+j+1)C(j,k), C(j,0)=1.

Equivalently,

v(1-v)F_j''+[2-(2j+2)v]F_j'-j(j+1)F_j=0.

Substituting F_j=(1-v)^(1-2j)N gives

v(1-v)N''+[2-(4-2j)v]N'-(2-j)(1-j)N=0.

For j>=2 the unique formal solution with N(0)=1 has coefficients

n_l=(1/(j-1))binom(j-1,l)binom(j-1,l+1), 0<=l<=j-2,

and zero thereafter: directly,

(l+1)(l+2)n_{l+1}=(l+2-j)(l+1-j)n_l.

At l=j-2 the right side vanishes, so the series terminates. This proves the finite formula without requiring any analytic hypergeometric continuation. For j=1, C(1,k)=1 and F_1=(1-v)^(-1) directly.
