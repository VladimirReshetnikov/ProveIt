# Sharp finite-height radius

Auxiliary theorem, 2 October 2026. Independently reviewed in audit/integrated-report-review.md. This theorem is not needed for either side of the leading global deficit proof.

Let A^[H](x) be the positive height-walk generating function restricted to macro-boundary heights 1,...,H, and rho_H its radius of convergence. Then

log(rho_H/rho) ~ (alpha/2) log(H)/H.          (1)

## Finite matrix and radius

Let K_H(x) be the H by H matrix of exact legal macro-transition generating functions. For fixed q,r,

[t^r]Q_q(x,t)=1_{r=0}
 +sum_{j=1}^q sum_{k=max(0,r-j)}^r
 C(j,k) binom(j,r-k) x^(r+k+1)/(1-x)^(j+r+k).

Thus every entry of K_H is rational and analytic on 0<x<1. All entries are positive there: take q=h and r=h'-1 to connect h to h'. They increase strictly with x. The Perron eigenvalue starts at zero and diverges as x->1. There is a unique rho_H in (0,1) at which it equals 1. The nonnegative initial vector and the positive terminal vector have positive Perron projections; Perron simplicity therefore gives a noncancelled pole in the restricted generating function. Hence its radius is rho_H. Similarity by the positive diagonal matrix diag(t_*^h) does not change the eigenvalue.

## Lower radius bound

Fix 0<delta<1 and put s_-=(1-delta)alpha logH/(2H), x_-=rho exp(s_-). At fixed critical t_*, uniform square-root transfer gives

Q_q(x_-,t_*) z_*^q
 <=C q^(-3/2) exp[q s_-/alpha+O(qs_-^2)].

The total row mass with q<=H differs from its critical mass m_*<1 by o(1): split q at H/(logH)^2. The lower range has exponentially tilted tail arbitrarily small, and the upper range contributes at most

C sqrt((logH)^2/H) H^((1-delta)/2)=o(1).

The fixed-q terms converge to their critical values. Therefore all rows of the diagonally tilted K_H(x_-) have sum below 1 for large H. Its Perron eigenvalue is below 1, so rho_H>x_-.

## Upper radius bound

Put s_+=(1+delta)alpha logH/(2H), x_+=rho exp(s_+). Choose gamma in (max(1/2,1-delta/2),1), let w=floor(H^gamma), and restrict to the height strip I=[H-w,H]. In each row retain q in [H-2w,H-w], all of which obey q<=h.

Uniform transfer gives

Q_q(x_+,t_*) z_*^q >=c H^(-3/2) H^((1+delta)/2)

throughout this q window: q/H->1, (w/H)logH->0, and qs_+^2=o(1).

At each such q, the tilted actual increment d=1+r-q has mean O(logH), variance asymptotic to nu q, nu=v/alpha>0. For each fixed real u, the analytic transfer expansion gives E exp(u d/sqrt(q)) -> exp(nu u^2/2) uniformly; its mean shift is O(logH/sqrtH)=o(1). The resulting weak Gaussian convergence therefore puts at least a fixed positive fraction of the mass in the inward increment window [0,sqrtH] or [-sqrtH,0], chosen according to which half of the height strip contains h. Since w/sqrtH->infinity, that window remains inside the strip. Consequently each restricted row sum is at least

c w H^(-3/2+(1+delta)/2)
 =c H^(gamma-1+delta/2) ->infinity.

The Collatz-Wielandt row bound gives a Perron eigenvalue greater than 1. Thus rho_H<x_+ for large H. Letting delta down to zero proves (1).

The fixed-q CLT here follows directly from the uniform analytic transfer formula for Q_q(x,T), since its logarithmic moment generating function has mean 1+O(logH/H) and variance nu+o(1) per q. Only weak convergence of the normalized r is needed for the positive inward intervals; no lattice local theorem is required.

No constant-order or log-log refinement of (1) is claimed.
