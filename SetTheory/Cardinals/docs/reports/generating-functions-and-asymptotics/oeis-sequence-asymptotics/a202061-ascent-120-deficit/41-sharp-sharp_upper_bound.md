# Sharp upper coefficient bound by a renewal calibration

Proof derivation, 2 October 2026. All uses of the exact positive representation refer to the unchanged foundation report. The leading-order argument has passed independent mathematical review; see audit/independent-audit.md.

## 1. Constants and exact tilted kernel

Write rho=1/mu, t=t_*=1/z_*, alpha as in the frozen report, and

v=(2 z_*^2-7 z_*+2)/2 > 0.

For L>=1, q>=1 and d an integer, let k(L,q,d) be the coefficient of x^L in

[x/(1-x)] [T^(d+q-1)] Q_q(x,T),

with a coefficient of negative T degree interpreted as zero. A step from h is legal exactly when q<=h; its endpoint is h+d>=1 automatically because r=d+q-1>=0. Define

w(L,q,d)=k(L,q,d) rho^L t^d.

The full critical row mass is

m=sum_{L,q,d} w(L,q,d)=rho/(b_* z_*+rho)<1.

The terminal weight at height h and unused length k is rho^k t^(1-h), apart from the original factor rho for the first letter. This terminal factor must be retained.

Let z_c(x,T) be the smaller positive zero of the discriminant of the quadratic defining Q. In a fixed real neighborhood of (rho,t), the discriminant roots remain distinct, positive and below 1, so the square-root transfer estimate is uniform:

Q_q(x,T) T^(-q) <= C q^(-3/2) exp(q Psi(s,theta)),
x=rho exp(s), T=t exp(theta),
Psi(s,theta)=-log(z_c(rho exp(s),t exp(theta)) t exp(theta)).

The exact root derivatives give

Psi(0,0)=Psi_theta(0,0)=0,
Psi_s(0,0)=1/alpha,
Psi_theta_theta(0,0)=v/alpha.

Consequently, uniformly near zero,

Psi(s,theta)=(s+v theta^2/2)/alpha
 +O(s^2+|s theta|+|theta|^3).                 (1)

The bounded positive prefactor [x/(1-x)]T does not affect these estimates. The coefficient asymptotic and these derivatives are proved in the accompanying kernel note.

## 2. Uniform local row lemma

Put

H=n^(2/3)(log n)^(1/3), F=H^2/n=n^(1/3)(log n)^(2/3).

Fix R,epsilon>0, 0<B<alpha/3, and a C^1 function f on [0,1]x[0,R] such that its first derivatives are uniformly continuous and

-f_s(s,y)+(v/2)f_y(s,y)^2 <= B/(y+epsilon).    (2)

For integer elapsed degree m, current height h, and legal next step (L,q,d), retain only transitions with m+L<=n and 1<=h+d<=RH. Define the transformed row weight

w(L,q,d) exp{F[f(m/n,h/H)-f((m+L)/n,(h+d)/H)]}.

Then all such row sums are at most some fixed m_bar<1 for all sufficiently large n, uniformly in m,h.

### Proof

Set a=F/n and b=F/H, so b^2=a and aH=log n. Both tend to zero. If L/n and |d|/H are at most a sufficiently small fixed eta, uniform differentiability gives

F[f(s,y)-f(s+L/n,y+d/H)]
 <= a[-f_s(s,y)+omega]L - b f_y(s,y)d + b omega |d|,      (3)

where omega can be made arbitrarily small, uniformly in s,y. For either sign of d, use the linear exponent in (3) with

lambda=a[-f_s+omega], theta=b[-f_y +/- omega].

Because B<alpha/3 and y ranges over a compact interval, choose omega so small that

lambda+(v/2)theta^2 <= a B'/(y+epsilon)

for one fixed B<B'<alpha/3. All these lambda,theta are bounded multiples of a,b. Formula (1) gives, uniformly q<=RH,

q Psi(lambda,theta) <= (B'/alpha)(log n) q/(h+epsilon H)+o(1).

Indeed q(a^2+ab+b^3)=O(H b^3)=O(n^(-1/3)(log n)^(4/3))=o(1).

The contribution with q>Q to either linear-majorant row tends uniformly to zero as first n and then Q tend to infinity. To see this, split at q=H/(log n)^2. Below this threshold, the exponential factor is 1+o(1), and the tail sum is O(Q^(-1/2)). Above it, use q/(h+epsilon H)<=1 and B'/alpha<1/3 to obtain

C (H/(log n)^2)^(-1/2) n^(B'/alpha)=o(1).

For q<=Q the exact transformed, truncated row has uniform limsup at most its unrestricted critical row, by domination with fixed-q generating functions in a fixed positive x-neighborhood of rho and T-neighborhood of t. More explicitly, first restrict L and d to a fixed finite set, on which the transformation tends uniformly to 1, and then make the remaining fixed-q exponentially bounded tail small. Near m=n the truncation may remove terms, so equality of the limiting rows is not asserted. Thus the small-step contribution has limsup at most m. Splitting into two signs only occurs in the q>Q tail, so it does not double the critical mass.

It remains to show that the excluded large normalized steps contribute o(1). Since f is globally Lipschitz on the compact rectangle, their exponent is bounded by C a L+C b |d|.

For L>eta n, apply an extra fixed positive length tilt s0. At fixed q<=RH the corresponding generating row is at most exp(C0 RH), uniformly for the vanishing height tilts +/-Cb. Chernoff gives a bound exp(-s0 eta n+O(H))=o(1).

For |d|>eta H, apply an extra small fixed signed height tilt theta0. At vanishing length tilt Ca and height tilt +/-Cb +/-theta0, (1) gives Psi<=C1 theta0^2+o(1). Choose theta0>0 sufficiently small that C1 R theta0^2<eta theta0/2. Chernoff then gives exp(-eta theta0 H/2+o(H))=o(1). The two signs cover both tails. These arguments use only q<=RH; summing over q contributes at most a polynomial factor. This proves a uniform row limsup <=m<1.

## 3. Coefficient consequence of the row lemma

Suppose additionally

f(1,y)<=P y

for some finite P, and f is Lipschitz in its first coordinate. Sum all finite transformed prefixes whose elapsed degree is at most n-1 and whose boundary heights stay <=RH. Their total weight is at most 1/(1-m_bar), by the positive Neumann/geometric expansion.

Telescoping the transformation along any such prefix of total length m and endpoint h gives the factor

exp{F[f(0,1/H)-f(m/n,h/H)]}.

The exact coefficient formula therefore yields

a_n^[<=RH] rho^n
 <= C exp(-F f(0,1/H)),                       (4)

because the residual terminal factor is uniformly bounded:

rho^(n-1-m) t^(1-h) exp(F f(m/n,h/H)) <= C.

Indeed f(s,y)<=P y+C(1-s), while F/H and F/n tend to zero. Thus the negative linear exponents from rho^(n-1-m) and t^(-h) dominate both terms for large n. No assumption that the entire walk ends at a small height is made.

The frozen first-hit estimate gives

a_n^[>RH] rho^n <= C exp[-R^2 F/(4D)]

for a fixed D. Hence, whenever R^2/(4D)>f(0,0), equations (4) and this first-hit estimate imply

liminf [n log(mu)-log a_n]/F >= f(0,0).        (5)

## 4. Explicit affine calibrations and the sharp constant

Take an increasing smooth bounded function p on [0,1], with p'>0. For B<alpha/3 and epsilon>0 define

f(s,y)=g(s)+p(s)y, g(1)=0,
g'(s)=v p(s)^2/2-2 sqrt(B p'(s))+epsilon p'(s).

The arithmetic-geometric mean inequality gives

-f_s+v f_y^2/2
 =2 sqrt(Bp')-p'(y+epsilon)
 <=B/(y+epsilon).

Thus (2) holds, while f(1,y)=p(1)y. Its initial value is

f(0,0)= integral_0^1 [2 sqrt(B p')-v p^2/2] ds
         -epsilon[p(1)-p(0)].                (6)

These calibrations approach the exact value

C(B)=3 (pi^2 B^2/(2v))^(1/3).

Here is an explicit demonstration. Set M=(2vB/pi^2)^(1/3), and parametrize the Kepler arch by

s=(u-sin(u)cos(u))/pi, y=M sin^2(u), 0<u<pi.

Then y'=pi M cot(u), y''=-vB/y^2. Set p_*(s)=-y'(s)/v. It is increasing, p_*'=B/y^2>0. Both p_*^2 and sqrt(p_*') are integrable at the two endpoints. Restrict p_* to [delta,1-delta] and linearly reparametrize this interval to [0,1]. The resulting p_delta is smooth, bounded, and increasing. As delta->0 its first integral in (6) converges to

integral [2B/y-y'^2/(2v)] ds
 =3B/M=C(B).

(The equality follows from y'^2/(2v)=B(1/y-1/M) and integral B/y ds=2B/M.) For each fixed delta let epsilon->0, then delta->0, then B->alpha/3. Choose a sufficiently large fixed R for each calibration. Equation (5) gives

liminf [n log(mu)-log a_n]/F
 >=(3 pi^2 alpha^2/(2v))^(1/3).               (7)

This is an upper coefficient bound with the conjectured sharp constant. It does not rely on a numerical fit, an unproved path-limit theorem, or a spectral identification from a discriminant alone. The local-row lemma and its use in this bound are covered by the independent audit.
