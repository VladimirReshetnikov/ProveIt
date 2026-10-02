# Candidate sharp third-term coefficient lower bound by independent rows and a central repair

Research draft, 2 October 2026. NOT independently audited and NOT part of the second-order release. The purpose is to close the missing o(M) global lower bound, or identify an obstruction in a specific lemma. No numerical fit is used.

## Target

Write L=log n, H=n^(2/3)L^(1/3), F=H^2/n and M0=F/L. Let cstar be the proved local-row constant and Y0=(2v alpha/(3pi^2))^(1/3). The target is

D_n <= C F[1+(7/3)log L/L+kappa/L+o(1/L)],
kappa=log Y0-2log 3+2cstar.

The key improvement over boxes is to retain the complete normalized tilted kernel, including the critical small-q mass mstar. At the row threshold, mass 1-mstar lies near q=h, but the remaining mstar cannot be discarded at o(M0) precision.

A reserved middle patch of r=M^(3/4) blocks repairs total physical degree and height exactly at o(M0) cost. It removes any need for an exact-sum local central limit theorem.

## 1. Smoothly interpolated legal cutoff and exact local threshold

Put h0=L^21 and eta=2/L^2. For real h>=h0 let u=(1-eta)h and define the nonnegative fractional cutoff

chi_h(q)=1 for q<=floor u;
chi_h(floor u+1)=u-floor u;
chi_h(q)=0 otherwise.

Fractional weights lie in [0,1], so they define a valid lower subkernel of the combinatorial kernel whenever its q values are legal. A real interpolation is solely a proof device, not a claim that combinatorial multiplicities are fractional.

In this note ell denotes the entire exact macro degree, including the leading x/(1-x) multiplier. It is not the internal block degree used in the local Gaussian lemma. With the exact critical-tilted macro kernel w(ell,q,d)=k(ell,q,d)rho^ell t_*^d, set

R_h(s,theta)=sum_{ell,q,d} chi_h(q) w(ell,q,d) exp(s ell+theta d).

Let V(h)>0 be the unique small positive root R_h(V(h),0)=1, and

N(h)=sum_{ell,q,d} q chi_h(q) w(ell,q,d)exp(V(h)ell).

The exact endpoint Laplace calculation from the proved finite-height note gives first the unrestricted-in-h statement in the actual cutoff u: V(h)=alpha/u[0.5log u+loglog u+cstar+epsilon(u)], where sup_{u>=(1-eta)h0}|epsilon(u)| tends to zero. Therefore, uniformly for h0<=h<=R H with fixed R,

V(h)=alpha/h [0.5log h+loglog h+cstar+o(1)],          (1)
N(h)=(1-mstar)h[1+o(1)].                            (2)

On this restricted range the eta cutoff changes the bracket in (1) by O(1/L), hence only o(1). For arbitrarily large h, only the global comparability V(h) asymp logh/h and the bounds below are used. The o(1) is uniform once h0 tends to infinity. Also V(h) is continuous, strictly decreasing and piecewise continuously differentiable. Differentiating the threshold equation on each interpolation interval gives

V'(h)=-(1-eta) A_{floor u+1}(V(h),0)/R_{h,s}(V(h),0).

Uniform differentiated transfer therefore implies

c log h/h^2 <= -V'(h) <= C log h/h^2,
|N'(h)|<=C log h,
c h<=N(h)<=C h.                                    (3)

To check the second derivative bound: the endpoint weight is O(log h/h); R_s is Theta(h); the q-weighted boundary term is O(log h); and |V'| times the q-length mixed moment is at most C(log h/h^2)h^2. The first inequality in (3) follows from the positive endpoint amplitude, not merely an upper transfer bound.

## 2. A one-dimensional energy minimum constructs the exact mean-flow arch

For Y>h0 define

J_n(Y)=n V(Y)+2sqrt(2/v) integral_{h0}^Y sqrt[V(h)-V(Y)] dh.   (4a)

The continuous function J_n tends to infinity as Y tends to infinity; the integral over h in [Y/4,Y/2] is at least c sqrt(Y logY). Also J_n(h0)=nV(h0) is much larger than F. For any physical-time trial path h(t)>=h0 with endpoints h0 and peak Y, the exact square inequality

h_dot^2/(2v)+V(h)
 >=V(Y)+|h_dot|sqrt{2[V(h)-V(Y)]/v}

implies its action is at least J_n(Y). In particular, the trial h0+H*y_Kepler(t/n) has action O(F), so J_n has an interior global minimum at some peak Y.

Differentiating the integral on each smooth cutoff interval is legitimate because its derivative is locally bounded by a constant times (Y-h)^(-1/2). One obtains

J_n'(Y)=V'(Y) [n-sqrt(2/v) integral_{h0}^Y [V(h)-V(Y)]^(-1/2) dh].

At interpolation junctions, both one-sided derivatives have the same bracket and strictly negative V' factors. Hence an interior minimizer, even at a junction, necessarily satisfies

n=sqrt(2/v) integral_{h0}^Y [V(h)-V(Y)]^(-1/2) dh.   (4)

Construct the ascending physical-time arch by h_dot=sqrt{2v[V(h)-V(Y)]}, and reflect it. Equation (4) makes its duration exactly n. Equality holds in the square inequality, so its action is J_n(Y); because J_n(Y) is the global minimum over peaks, this is also a global minimizer of the physical-time action. This argument needs neither a nonsmooth Euler-Lagrange theorem nor differentiation of the threshold asymptotic remainder.

Its peak obeys Y=Theta(H). The upper bound follows from kinetic coercivity and J_n(Y)=O(F). If Y<=sqrt(n), the lower bound nV(Y) already exceeds O(F); hence logY>=L/2 for large n. Then nV(Y)<=O(F) implies Y>=cH. Put lambda=V(Y).

Define theta=+/-sqrt{2[V(h)-lambda]/v} along the ascending/descending physical-time curve, and introduce the macro coordinate by

dt/dj=N(h)/alpha.

Thus dh/dj=(v/alpha)N(h)theta=:f(h), with the appropriate sign. Its continuous macro duration is

m=2 integral_{h0}^Y dh/[ (v/alpha)N(h)sqrt{2[V(h)-V(Y)]/v} ].

Using (3), split at Y/2 to see m=Theta(sqrt(Y/logY))=Theta(M0). Below Y/2, V(h)-V(Y) is comparable to logh/h; above it, the difference is comparable to (L/Y^2)(Y-h). These same comparisons will control the endpoint concentration estimates.

Round m to an integer M and reparameterize the curve by j in [0,M], changing its speed by 1+O(1/M). Denote sampled heights h_j and signed momenta theta_j. They satisfy h_0=h_M=h0, h_j=h_{M-j}, theta changes continuously from positive to negative, and

|theta_j|<=C sqrt(L/h_j),
|d theta/dj|<=C L/h_j,
|d^2h/dj^2|<=C L^2.                                (5)

These follow from (3), f=f(h), and the identity

d theta/dj = N(h)V'(h)/alpha

before the harmless reparameterization. The apparent square-root singularity at the peak cancels. Its second height derivative is

f f'=(v/alpha)^2[N N' theta^2+N^2 V'/v]=O(L^2).

This energy-minimum construction deliberately avoids differentiating an uncontrolled o(1) term in the threshold asymptotic, avoids nonsmooth variational regularity issues, and needs no uniqueness or sharp perturbation expansion for a duration-equation root.

## 3. Independent row laws along the deterministic arch

For each j use the full distribution on (ell,q,d) proportional to

chi_{h_j}(q) w(ell,q,d) exp(lambda ell+theta_j d),

and call its row mass R_j. Differentiable square-root transfer gives, uniformly over the entire arch,

R_j=1+O(L^(3/2)/sqrt(h_j))=1+o(1),                 (6)
E d_j=(v/alpha)N(h_j)theta_j+O(L^2),                (7)
E ell_j=N(h_j)/alpha+O(L^(3/2)sqrt(h_j)).           (8)

Here is the needed uniform comparison. The exact fixed-q row is

A_q(s,theta)=a(s,theta)q^(-3/2)exp(q Psi(s,theta))
             (1+O(q^-1)),

with differentiated uniformity. Its analytic reduced factor A_q exp(-q Psi) has uniformly bounded logarithmic first derivatives for all q after the finitely many small q are included. Since

lambda+v theta_j^2/2=V(h_j),

one has Psi(lambda,theta_j)-Psi(V(h_j),0)=O((L/h_j)^(3/2)). Multiplication by q<=h_j yields the error in (6). The mean d follows from Psi_theta=nu theta+O(lambda+theta^2), with nu=v/alpha. Changing the q mean by the row comparison costs at most theta*h*O(L^(3/2)/sqrt h)=O(L^2). The length derivative Psi_s=alpha^-1+O(|theta|+lambda) gives (8), including the same row-comparison error.

Under these laws the centered increment and length logarithmic moment generating functions obey

log E exp(z(d-E d)) <= C z^2 h_j L,
                    |z|<=c/sqrt(h_j L),
log E exp(z(ell-E ell)) <= C z^2 h_j^2,
                    |z|<=c/h_j.                  (9)

One way to prove (9) is to differentiate the exact row twice throughout the indicated tilted intervals. At fixed q the increment variance is O(q), its conditional mean is O(q sqrt(L/h)); variation of that mean over q<=h contributes at most O(hL). For length, both its conditional variance and the variance of its conditional mean are O(h^2). The same bounds hold under the small additional tilt. Taylor's theorem for the normalized log row gives (9).

## 4. Leave a central repair interval unsampled

Let r be the smallest integer at least M^(3/4) with r congruent to M modulo 2, and remove the r consecutive positions from a=(M-r)/2 through b-1=(M+r)/2-1. Sample all remaining positions independently from the row laws. View the left half forward from the seed height floor h0 and the right half backward from that same terminal seed height. Their starting heights are reconstructed from the sampled d's.

With probability tending to one, all sampled blocks are legal and their boundary-height errors satisfy

|E_j|<=h_j/(10L^2).                                (10)

Here are sufficient quantitative estimates rather than an appeal to a path limit. On the ascending half while h<=Y/2, (1)-(3) imply f(h)>=c sqrt(h log h), whence the number of preceding blocks is O(sqrt(h/log h)) and

sum preceding h_i L <= C L h^(3/2)/sqrt(log h).

The deterministic drift mismatch between (7) and the sampled increments of the curve is at most O(L^2) per position, plus the reparameterization contribution O(h/M). Thus its prefix is at most

C L^2 sqrt(h/log h)+O(h/M)=o(h/L^2)

uniformly for h>=h0=L^21. Bernstein's inequality from (9), with threshold h/(20L^2), has exponent at least

c sqrt(h log h)/L^5 >=c L^(11/2)sqrt(log L),

up to inessential constants. Near the peak, the coarser bounds variance O(nL) and threshold cH/L^2 give exponent at least cF/L^5, which is much larger than L. The union bound over M=exp(O(L)) boundaries still tends to zero. The descending half uses its complementary suffix from the fixed endpoint, identically. No conditioning is needed.

Every retained q is at most ceil((1-2/L^2)h_j)<=h_j-h_j/L^2 for large n, hence below the actual starting height under (10). Endpoint positivity is automatic. This argument also covers the last sampled position before the central repair and first after it.

Two additional high-probability bounds are sufficient:

|sum sampled ell - sum sampled E ell|<=L H sqrt M,
|central endpoint-height mismatch|<=L sqrt(nL).     (11)

The first follows from the length variance in (9), the second from the increment variance and (7); Chebyshev is already enough. The deterministic total height bias O(ML^2) is o(sqrt(nL)). The parity choice makes the two deterministic patch-edge heights exactly equal: h_a=h_b.

## 5. Exact physical-degree and height repair costs o(M)

Let X be the sampled total physical degree. The two exact seeds and the original first letter have total degree 2floor(h0)+1. Set

D=n-[2floor(h0)+1]-X.

The sampled mean-degree sum differs from its deterministic physical integral by O(HL): this follows from (8), integral sqrt(h) dj=O(M sqrt H), and the total-variation quadrature bound |N'|<=CL. The missing middle portion has expected degree

r (1-mstar)Y/alpha [1+o(1)].

Since r>>L sqrt M and r>>L, (11) implies

D/(rY) -> (1-mstar)/alpha                           (12)

uniformly on a subset whose probability tends to one. In particular D>0.

Choose r integer patch total degrees L_i summing to D and differing by at most one; for the local Gaussian lemma use internal block degrees ell_i=L_i-1 and retain its leading x term. Thus the sampled rows and the patch both count full physical degree exactly; there is no unaccounted one-unit shift per sampled macro-block. Choose r integer increments summing to the exact endpoint-height difference Delta and differing by at most one. Linear interpolation keeps every patch boundary at Y[1+o(1)]. By (12), every shifted q-saddle lies at

q=(1-mstar)Y[1+o(1)]

and therefore has a fixed positive legality margin. Also

|d_i|<=|Delta|/r+1=o(sqrt(YL)),

so the audited local positive Gaussian lower bound applies. The total patch cost in the critical tilt is at most

C r L+C Delta^2/(rY)
 <=C r L+C M L^3/r=o(M).                           (13)

This patch enforces exactly the desired total physical degree and the return to the seed height for every retained outside realization. It does not require a local limit theorem, a polynomial exact-sum probability, or an unbounded endpoint repair. All patch degrees and increments are integers. There is no overcounting: M and the patch positions are fixed, and deleting those positions from any completed marked macro-path recovers its outside data. The exact positive macro-path expansion already counts block multiplicities; selecting a fixed patch length/increment pattern and summing its legal q-window is a subset of that expansion. Each outside fractional chi factor is at most 1, so these weighted contributions remain lower bounds on the original positive coefficients.

## 6. Removing tilts and evaluating the deterministic action

The sampled product of original critical weights is the product probability times

exp[-lambda sum sampled ell-sum sampled theta_j d_j]
 times prod sampled R_j.

By (6), sum log R_j=o(M). The difference between lambda times the sampled degree and lambda n is O(rL)+polylog(n)=o(M), because lambda=O(L/H) and the patch degree is O(rH).

Write g_j=h_{j+1}-h_j. On each sampled interval, summation by parts and (5),(10) give

sum theta_j(d_j-g_j)=o(M).                          (14)

The interior error is bounded by C sum (L/h_j)(h_j/L^2)=O(M/L). The two central boundary terms are O(r/L): near the peak theta=O((r/M)sqrt(L/H)), while |E|<=CH/L^2 and sqrt(HL)=Theta(ML). The seed boundary terms are only polylogarithmic.

The omitted deterministic middle action is O(rL)=o(M). A Stieltjes quadrature estimate gives

sum theta_j g_j
 =2 sqrt(2/v) integral_{h0}^Y sqrt(V(h)-V(Y)) dh+o(M). (15)

For example, its error is bounded by the integral of |theta'| |h'| in macro time, which is O(integral_{h0}^Y L/h dh)=O(L^2), plus endpoint roundings. This is o(M).

Summing over the retained independent realizations of probability 1-o(1), inserting the exact patch and seeds, and using (13)-(15) proves the candidate bound

D_n <= J_n(Y)+o(M),
J_n(Y)=n V(Y)+2 sqrt(2/v) integral_{h0}^Y sqrt(V(h)-V(Y)) dh,   (16)

where Y solves (4). All occurrences of M are Theta(M0), so o(M)=o(F/L).

## 7. Evaluate only an explicit trial action

There is no need to expand the perturbed minimizing peak. The expression J_n(Y) in (16) is exactly the minimizing physical-time action constructed by (4a) and the square inequality. It is therefore bounded above by the explicit trial

h_trial(t)=h0+H y_*(t/n),

y_*(s)=Y0 sin^2 u,
s=(u-sin u cos u)/pi,
Y0=(2v alpha/(3pi^2))^(1/3).

Uniformly for h=Hy with L^-6<=y<=R,

(n/F)V(Hy)
 =alpha/(3y)
  +alpha/(2Ly)[(7/3)log L+log y+2log(2/3)+2cstar+o(1)],        (17)

where the row-threshold o(1) is uniform and the elementary loglog-expansion remainder is O((logL+|logy|)/L)=o(1) in the bracket. The addition of h0 changes these integrals by o(F/L), since h0/H is smaller than every inverse fixed power of L.

The endpoint portions y<=L^-6 contribute O(F/L^3)+polylog(n)=o(F/L) to the trial action. For the potential, use V(h)<=C logh/h and y_*(s) comparable to s^(2/3); the ultra-short portion H y<=h0 is only polylogarithmic. The kinetic endpoint integral has the same O(F/L^3) bound. Thus (17) may be integrated along the full leading arch at o(F/L) error.

The leading kinetic plus potential action is C F. Furthermore

(alpha/2) integral_0^1 ds/y_*(s)=C,
weighted average of log y_*(s) = logY0-2log2,

because ds/y_*=2du/(pi Y0). Therefore the trial action is

C F[1+(7/3)logL/L+(logY0-2log3+2cstar)/L]+o(F/L).    (18)

Combining its upper bound for the minimizing action with (16) gives the targeted one-sided third-term deficit bound. No differentiability of the remainder in (1), no moving-peak expansion, and no exact-sum local central limit theorem is required.

## Audit targets / possible obstructions

This is intended as a nearly complete proof plan, not an approved theorem. The following must be checked explicitly:

1. All differentiated uniform transfer comparisons, including the all-q reduced-factor bound used in (6)-(8), and the fractional-cutoff derivative bounds (3)
2. Quantitative construction of the piecewise-smooth mean-flow arch and its rounded sampling, especially the uniform prefix/suffix drift-error estimates near h0
3. The total-variation quadrature estimate O(HL) for physical degree, and the high-probability patch-length limit (12)
4. That different outside realizations and their deterministic patches are counted without overcounting in the exact positive macro-path representation
5. The elementary one-dimensional energy-minimum argument and one-sided derivative condition at interpolation junctions, plus explicit-trial integration in Section 7; these avoid moving-peak expansion or differentiation of the threshold remainder

A failure of any of these would obstruct the claimed third-term lower bound. The second-order release is unaffected.
