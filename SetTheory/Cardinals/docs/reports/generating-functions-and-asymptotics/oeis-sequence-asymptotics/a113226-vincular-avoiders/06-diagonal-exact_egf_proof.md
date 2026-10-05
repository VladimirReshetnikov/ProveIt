# A113226: an exact continuous-rank generating function

Derivation underlying the accompanying article, 2026-10-01. The exact state argument and its algebra have been checked separately by direct mathematical derivation.

Let a_n count permutations avoiding the vincular pattern 12-34: there do not exist i,j with i+1<j and pi_i<pi_(i+1)<pi_j<pi_(j+1). Put A(z)=sum a_n z^n/n!.

## Exact continuation states

Use independent continuous uniform labels on (0,1). Every order type of n labels has probability 1/n!, so its avoidance probability is a_n/n!. After a nonempty allowed prefix, let y be its last label and m the minimum of all ascent tops seen so far; if there has been no ascent, put m=1. A new ascent beginning at y is allowed exactly when y<=m. This includes equality: when y=m, the record ascent ending at y and the proposed next ascent overlap, and cannot by themselves form a four-entry occurrence.

Let F(m,y;z) be the generating function for allowed continuations, including the empty continuation. The diagonal value G(m;z)=F(m,m;z) must be retained separately. Its state is attained on a positive-probability set of prefixes even though the diagonal has two-dimensional Lebesgue measure zero. In integrals below, off-diagonal values are used except where a transition explicitly lands on the diagonal.

For |z|<1, all continuation series converge absolutely and uniformly, being bounded by 1/(1-|z|). Directly appending a label gives, for 0<y<m,

F(m,y)=1+z int_0^y F(m,u)du+z int_y^m G(u)du+z int_m^1 F(m,u)du.       (1)

For m<y<1,

F(m,y)=1+z int_0^y F(m,u)du.                                      (2)

At the diagonal,

G(m)=1+z int_0^1 F(m,u)du.                                        (3)

Indeed, in (1), a descent keeps m, an ascent whose new top u<m creates state (u,u), and an ascent to u>m keeps m. In (2), only descents are permitted. In (3), every append is permitted and m stays fixed except at a null equality.

Set H(m)=1+z int_0^m F(m,u)du. Equation (2) implies

F(m,y)=H(m)exp(z(y-m)), y>m;
G(m)=H(m)exp(z(1-m)).                                             (4)

The left limit of (1) at y=m is G(m), and differentiation in y gives partial_y F=z(F-G(y)). Therefore

F(m,y)=exp(z(y-m))G(m)+z exp(zy)int_y^m exp(-zu)G(u)du, y<m.        (5)

Integrating (5) from 0 to m yields

H(m)=1+(1-exp(-zm))G(m)+z int_0^m(1-exp(-zu))G(u)du.

Combining with (4),

D(m)G(m)=1+z int_0^m(1-exp(-zu))G(u)du,
D(m)=exp(z(m-1))+exp(-zm)-1.                                     (6)

Near z=0, D is nonzero uniformly on m in [0,1]. Equation (6) gives G(0)=exp(z), and differentiating gives

G'(m)/G(m)=z(1-exp(z(m-1)))/D(m).                                 (7)

Let E=exp(z), x=exp(zm), and P_E(x)=x^2-Ex+E. Then

d log G=(E-x)/P_E(x) dx,
log G(1)=z+int_1^E (E-x)/P_E(x) dx.

Since int_1^E (2x-E)/P_E(x) dx=log P_E(E)-log P_E(1)=log E=z,

log G(1)=int_1^E x/P_E(x) dx.                                    (8)

Starting from the empty permutation and appending the first uniform label gives

A(z)=1+z int_0^1 F(1,y)dy=H(1)=G(1).

Thus, as an analytic germ at zero and hence as a formal power series,

                 A(z)=exp(T(z)),
 T(z)=int_1^(exp z) x/(x^2-exp(z)x+exp(z)) dx.                     (9)

The derivation proves the identity on a neighborhood of zero; all later analytic continuation claims must be established from (9), rather than assumed from the original continuation integral outside |z|<1.

## Relation with Elizalde's published envelopes

Elizalde, *Asymptotic enumeration of permutations avoiding generalized patterns*, Adv. Appl. Math.36 (2006),138-155, Proposition5.1, defines b_0=z, c_0=exp(z)-1-z and b_k''=k^2 exp(z)b_(k-1), c_k''=k(k+1)exp(z)c_(k-1), with zero initial values for k>=1. His coefficientwise bounds are exp(S)<A<exp(S+exp(z)+z-1), S=sum_(k>=1)(b_k+c_k).

There are direct integral representations

b_k(z)=int_0^z (exp(u)-1)^k(exp(z-u)-1)^k du,
c_k(z)=int_0^z (exp(u)-1)^(k+1)(exp(z-u)-1)^k du.

They follow either by placing a distinguished threshold label among the labeled decreasing blocks, or by checking the displayed differential recurrences and initial conditions. Summing the geometric series near z=0 gives

sum_(k>=0)(b_k+c_k)=int_0^z exp(u)/[1-(exp(u)-1)(exp(z-u)-1)]du=T(z).

Therefore (9) places A exactly between the published envelopes, with T=S+exp(z)-1. This equality is derived independently above and is not inferred from those bounds.

Primary PDF: https://math.dartmouth.edu/~sergi/papers/pp05_aam_elizalde.pdf

## Singularity calculation and link to the coefficient proof

For real 0<z<rho=log4, Delta=E(4-E)>0 and

T(z)=z/2+E/sqrt(Delta) [atan(E/sqrt(Delta))-atan((2-E)/sqrt(Delta))].

As delta=rho-z decreases to zero,

T(z)=pi/sqrt(delta)+rho/2-3+O(sqrt(delta)).                        (10)

Thus an ordinary essential-singularity saddle would predict

a_n/n! ~ C rho^(-n) exp(alpha n^(1/3)) n^(-5/6),
alpha=3(pi^2/(4rho))^(1/3),
C=exp(rho/2-3) (pi/(2sqrt(rho)))^(1/3)/sqrt(3pi).

The contour/minor-arc proof and explicit treatment of analytic branches are supplied in all_orders_proof.md and the article. The full expansion uses powers n^(-1/3), with inversion around the Gamma core for n! rho^(-n). The coefficient asymptotic is not inferred solely from (10).

## Source status

OEIS https://oeis.org/A113226 currently gives the same counting problem and cites the 2025 paper below; no closed EGF was found in its displayed formulas.

Bevan–Cheon–Kitaev, *On naturally labelled posets and permutations avoiding 12-34*, European J. Combin.126 (2025),104117, DOI10.1016/j.ejc.2024.104117, Conjectures13–14, still conjecture the growth constant 1/log4 and a stretched-exponential equivalent. Their Proposition11 uses exactly the lowest-ascent-top/last-entry state but for a trivariate ordinary generating function. The uniform-label integral route above is a continuous-rank reformulation of that same insertion mechanism. It must be credited as such.

Primary PDF: https://pure.strath.ac.uk/ws/portalfiles/portal/256336418/Bevan-etal-EJC-2025-naturally-labelled-posets-and-permutations-avoiding-12-34.pdf

Bounded live searches on 2026-10-01 for A113226, 12-34 generating functions, and the 2025 conjectures did not locate a later proof. This does not establish absence of a proof elsewhere.
