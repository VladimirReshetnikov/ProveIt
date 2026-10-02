# An explicit constant in the finite-height radius shift

Research proof, 2 October 2026. This is a new refinement, not covered by the frozen release's audit. It should be reviewed independently. The global coefficient deficit result does not require this auxiliary theorem.

## Statement and constants

Use the exact positive macro-kernel and critical constants from the frozen release. Write

z=z_*, rho=1/mu, t=1/z, b=1-rho,
alpha=(8z^2-29z+9)/7,
C_q=sqrt(-16z^2+55z-10)/(2sqrt(pi)),
m_*=rho/(bz+rho),
a_*=rho t C_q/(1-rho),
c_*=log[(1-m_*)/(2a_*)].

Numerically,

m_*=0.4450418679126288085778051289935895...,
a_*=0.1166233191761628160392820802228155...,
c_*=0.8667962458055399529886348076493374... .

Let rho_H be the radius of the exact macro-boundary-height-restricted generating function on heights 1,...,H. Then

log(rho_H/rho)
 =alpha/H [0.5log H+loglog H+c_*+o(1)].             (T)

The same formula holds for the unique positive length tilt at which the unrestricted-destination row with q<=H has total mass 1. The equality of these constants is proved below by a cosine test on a narrow high strip; it is not inferred from a row sum alone.

## 1. Exact tilted row and uniform transfer with derivatives

Let k(L,q,d) denote the nonnegative exact macro-transition coefficients. At x=rho exp(s), define

A_q(s,theta)=sum_{L,d} k(L,q,d)x^L(t exp(theta))^d
 =xT/(1-x) Q_q(x,T)T^(-q), T=t exp(theta).

For (s,theta) in a sufficiently small fixed complex neighborhood of (0,0), the two discriminant roots remain separated, the smaller root z_c is analytic, and all rational prefactors stay away from their poles. The square-root coefficient expansion therefore gives

A_q(s,theta)=a(s,theta)q^(-3/2)exp[q Psi(s,theta)]
             (1+O(q^(-1))),                         (1)

where

Psi(s,theta)=-log[z_c(rho exp(s),t exp(theta))t exp(theta)],
a(s,theta)=xT C_q(x,T)/(1-x), a(0,0)=a_*.

The expansion and its first four parameter derivatives hold uniformly after shrinking the neighborhood. This follows directly from the explicit square-root expression: expand its analytic multiplier at z_c, use the exact binomial coefficients of (1-z/z_c)^(1/2), and bound the remaining analytic convolution uniformly. The error is analytic in the parameters with uniform O(q^(-1)) bound in the larger neighborhood, so Cauchy's formula gives the same derivative bound on the smaller one.

The known discriminant derivatives imply

Psi(0,0)=Psi_theta(0,0)=0,
Psi_s(0,0)=1/alpha,
Psi_thetatheta(0,0)=nu=v/alpha>0.

In particular, for s=O(log H/H),

Psi(s,0)=s/alpha+O(s^2),
Psi_theta(s,0)=O(s),
Psi_thetatheta(s,0)=nu+O(s).                         (2)

The finitely many small q not covered by a selected uniform asymptotic cutoff are analytic on a common fixed neighborhood and satisfy all corresponding bounded moment estimates directly.

## 2. Exact endpoint Laplace sum and row threshold

For a fixed real c set

s_H(c)=alpha/H [0.5log H+loglog H+c],
R_H(c)=sum_{q=1}^H A_q(s_H(c),0).

Then

R_H(c) -> m_*+2a_* exp(c),                          (3)

locally uniformly in c. The same limit holds if H in the upper summation limit is replaced by H-W, where W log H/H ->0.

Here is a direct derivation. Put k=H Psi(s_H(c),0), so by (2)

k=0.5log H+loglog H+c+o(1).

For q<=H/(log H)^2 the exponential multiplier differs from 1 by o(1) uniformly, and summable q^(-3/2) bounds give the limiting critical contribution. The range H/(log H)^2<q<=H/2 contributes o(1): its total is bounded by C(log H)/sqrt(H) exp(k/2)=o(1). On H/2<q<=H, the asymptotic (1) and the elementary endpoint sum yield

sum q^(-3/2)exp(kq/H)
 =H^(-1/2)exp(k)/k [1+O(1/k)+o(1)]
 ->2exp(c).                                        (4)

To verify the endpoint sum, write q=H-r; the relevant geometric window has r=O(H/k), on which (1-r/H)^(-3/2)=1+O(r/H), and sum exp(-kr/H)=H/k[1+o(1)]. The range r larger than a slowly growing multiple of H/k is negligible. Critical mass from q>H/2 vanishes, so adding the fixed-q limit produces (3), without double counting.

Since c_* solves m_*+2a_*exp(c_*)=1, and the row sum strictly increases in s, (3) proves the asserted unrestricted-destination row-threshold formula.

For the radius lower bound, if c<c_* then every diagonally tilted row of the height-H matrix at x=rho exp(s_H(c)) has mass at most R_H(c)<1 for large H. Thus its Perron eigenvalue is below 1 and rho_H>rho exp(s_H(c)).

## 3. A homogeneous increment kernel in a high strip

Fix c>c_* and choose any fixed gamma with 1/2<gamma<1. Set

W=floor(H^gamma), Q=H-W,
I={H-W+1,...,H}, x=rho exp(s_H(c)).

For every starting height in I all choices q<=Q are legal. Define the homogeneous increment weights

a_d=sum_{q=1}^Q sum_L k(L,q,d)x^L t^d,
R=sum_d a_d.

The second assertion of (3) gives

R -> m_*+2a_*exp(c)>1.                              (5)

We need the following uniform moment estimates:

sum_d a_d d=O(log H),
sum_d a_d d^2=Theta(H),
sum_d a_d |d|^3=O(H^(3/2)),
sum_d a_d exp(c1|d|/sqrt(H))<=C                    (6)

for some fixed c1,C>0.

For completeness, at fixed q the normalized increment distribution has moment generating function A_q(s,theta)/A_q(s,0). Differentiating (1)-(2) gives mean O(1+qs), variance nu q+O(qs+1), and bounded higher cumulants O(q+1). Evaluating the same ratio at theta=+/-c1/sqrt(H) gives a bounded exponential moment uniformly for q<=H: the logarithm is O(qs/sqrt(H)+q/H+H^(-1/2))=O(1). Summing with the row weights proves the exponential bound, the upper second and third bounds, and the mean bound. The lower second bound follows because (4) assigns a fixed positive mass to q in [H-O(H/log H),Q], where the conditional variance is at least cH.

The exponential moment also gives, for each fixed integer r>=0,

sum_{|d|>W} a_d |d|^r
 <=C_r H^(r/2)exp[-c2 W/sqrt(H)]=o(1).              (7)

We use only r=0,1,2,3. Such bounds follow by spending half the exponential moment to dominate the polynomial |d|^r.

## 4. Centering the sine transform with a tiny exponential tilt

Put delta=pi/(W+1), and truncate increments to |d|<=W. Define

S(tau)=sum_{|d|<=W} a_d exp(tau d)sin(delta d).

Because sin(delta d) has the same sign as d in this range,

S'(tau)=sum a_d exp(tau d)d sin(delta d)>0.

By |sin u-u|<=|u|^3/6 and (6)-(7),

S(0)=O(delta log H+delta^3 H^(3/2)).                 (8)

For any fixed sufficiently small epsilon>0 and |tau|<=epsilon/sqrt(H),

S'(tau)>=c delta H.                                (9)

Indeed, choose a large fixed B. The second moment in |d|<=B sqrt(H) is at least cH, using (6) and its exponential tail bound. In that range exp(tau d)>=exp(-epsilon B), and, for large H, d sin(delta d)>=delta d^2/2 because sqrt(H)/W->0. This proves (9).

Since the ratio of (8) to the lower derivative bound in (9) is

O(log H/H+H^(1/2)/W^2)=o(H^(-1/2)),

the intermediate value theorem gives a unique root tau_H of S with

|tau_H|=O(log H/H+H^(1/2)/W^2)=o(H^(-1/2)).         (10)

At that root put

C_H=sum_{|d|<=W}a_d exp(tau_H d)cos(delta d).

Then

C_H=R+o(1).                                        (11)

The omitted tail is o(1) by (7). The exponential-tilt error is at most

|tau_H| sum a_d |d|exp(|tau_H d|)=O(|tau_H|sqrt H)=o(1),

and the cosine error is O(delta^2 H)=o(1), by the same exponential moments.

## 5. Cosine-test Perron lower bound

Index the strip I by i=1,...,W and take the positive vector

f_i=sin(delta i).

Extend it by zero outside 1,...,W. For i in the strip and |d|<=W,

f_{i+d}>=sin(delta(i+d)).                            (12)

Inside the strip this is equality; just outside it the right side is nonpositive, since 1-W<=i+d<=2W. Consequently the restricted, tilted homogeneous matrix B_H obeys

(B_H f)_i
 >=sum_{|d|<=W}a_d exp(tau_H d)sin(delta(i+d))
 =f_i C_H+cos(delta i)S(tau_H)
 =C_H f_i.

Collatz-Wielandt therefore yields r(B_H)>=C_H. This matrix is obtained by retaining only some transitions of the original height-H matrix and applying positive diagonal similarities, so positivity and spectral-radius monotonicity imply

r(K_H(x))>=r(B_H)>=C_H=R+o(1)>1

by (5). Hence rho_H<rho exp(s_H(c)) for all sufficiently large H.

Together with the lower bound for every c<c_*, letting c decrease/increase to c_* proves (T). The restricted generating function's radius is the unique x at which r(K_H(x))=1, as already established in the frozen finite-height theorem.

## Scope warning

The explicit c_* here is a finite-height/local-row constant. It has not been shown to equal a coefficient in the global deficit's O(n^(1/3)(log n)^(-1/3)) remainder. Determining that global constant requires a sharper matching coefficient lower construction or another global argument that retains all O(number of macro-blocks) terms.
