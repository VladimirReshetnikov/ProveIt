# Canonical full-cut sectors for the A113226 EGF

Research proof note. The delivered source ZIP is unchanged. This note starts from its exact identity and does not reinterpret a finite dominant asymptotic truncation as an exact sector.

## 1. Global branch and its singularities

Write

- rho = log 4;
- zeta_k = rho + 2 pi i k;
- epsilon_k = (-1)^k;
- g_k = (3-epsilon_k)/2, so g_k=1 for even k and g_k=2 for odd k.

On the t-plane cut along (-infinity,-2] and [2,infinity), take the branches of sqrt(4-t^2) and asin(t/2) that are positive at t=0 and zero at t=0, respectively. Define

F(t) = t exp{(3 asin(t/2)-pi/2)t/sqrt(4-t^2)},
A(z) = F(exp(z/2)).

This is a single-valued holomorphic function on

D = C minus union_{k in Z} (zeta_k+[0,infinity)).

It agrees with the delivered EGF near z=0. Indeed, on the real interval z<rho, putting w=sqrt(4 exp(-z)-1), one has asin(exp(z/2)/2)=pi/2-atan(w), and hence

log A(z) = z/2 + (pi-3 atan(w))/w.

The identity extends from this interval by analytic continuation. The t-representation gives A(z+4 pi i)=A(z) and A(conj z)=conj A(z). For a 2 pi i shift, F(-t)=-F(t) exp(pi t/sqrt(4-t^2)); equivalently, along compatible logarithmic determinations, T(z+2 pi i)-T(z)=pi i+pi t/sqrt(4-t^2). Thus odd and even singularities have different local strengths.

For small delta in C\(-infinity,0], with the principal sqrt(delta), the branch near zeta_k is exactly

T_k(zeta_k-delta)
 = (zeta_k-delta)/2
   + g_k pi/sqrt(exp(delta)-1)
   - 3 atan(sqrt(exp(delta)-1))/sqrt(exp(delta)-1),
A(zeta_k-delta)=exp(T_k(zeta_k-delta)).

Here the quotient atan(w)/w is analytic in w^2 near zero. In particular,

T_k(zeta_k-delta)
 = g_k pi delta^(-1/2) + T0_k
   -(g_k pi/4)delta^(1/2) + delta/2 + O(delta^(3/2)),
T0_k = zeta_k/2-3.

The assertion is for the exponential and is insensitive to changing T_k by an integral multiple of 2 pi i. The stated choice retains the factor exp(zeta_k/2)=2(-1)^k.

## 2. Exact bank values, including endpoint behavior

For x>0 put

q(x)=sqrt(1-exp(-x)),
L(x)=artanh(q(x))=arcosh(exp(x/2)),
B_cut(x)=2 exp(x/2) exp[-3 L(x)/q(x)].

The upper and lower bank limits are

A_k^+(x)=epsilon_k B_cut(x) exp[+i g_k pi/q(x)],
A_k^-(x)=epsilon_k B_cut(x) exp[-i g_k pi/q(x)].

For example, the upper bank corresponds to delta=-x-i0, so sqrt(exp(delta)-1)=-i q and 1/sqrt(exp(delta)-1)=i/q. These formulas fix the signs, not just the moduli.

One has

B_cut(x) -> 2 exp(-3) as x downarrow 0,
B_cut(x) = (1/4) exp(-x)[1+O(x exp(-x))] as x -> infinity.

Thus B_cut is bounded and integrable on (0,infinity), uniformly in k. Both individual bank values have leading behavior -(1/4)exp(-x) at infinity. The bank-jump integral therefore converges absolutely even at the endpoint. It is nevertheless not a full Hankel contribution: the essential endpoint loop cannot simply be discarded.

## 3. Definition and orientation of the canonical sectors

Fix 0<r<min(rho/2,pi), taking it still smaller if desired. Let C_k(r) be the clockwise circle centered at zeta_k, starting at the lower bank of zeta_k+r and ending at its upper bank. More precisely, in delta=zeta_k-z coordinates it is delta=r exp(i alpha), with alpha decreasing from pi to -pi, and with bank limits at the endpoints.

For integer n>=1 define

H_k(n) = (1/(2 pi i)) [
  integral_{C_k(r)} A(z) z^(-n-1) dz
  + integral_r^infinity [A_k^+(x)-A_k^-(x)](zeta_k+x)^(-n-1) dx
].

The complete path is lower bank from infinity toward r, the clockwise endpoint circle, then upper bank from r toward infinity. This is the clockwise full-cut contribution. For the test integrand A(z)=1/(rho-z), the circle gives -Res_{rho}(A(z)z^(-n-1))=rho^(-n-1), verifying the sign.

Cauchy's theorem in the cut annulus between any two admissible radii proves that H_k(n) does not depend on r. No limit r->0 is needed. In particular, an n-dependent radius may later be chosen for saddle analysis. If a shrinking-loop limit is considered, radius independence and integrable bank values imply its existence, but do not imply that this limit is zero.

## 4. Exact sum and absolute convergence

On horizontal lines Im z=(2j+1)pi, exp(z/2) is purely imaginary. If s=exp(x/2), the common modulus is

B_strip(x)=s exp[-3 s asinh(s/2)/sqrt(4+s^2)].

It is O(exp(x/2)) as x->-infinity and O(exp(-x)) as x->infinity, so M=int_R B_strip(x) dx is finite. Also A(z)=O(exp(Re z/2)) uniformly in Im z as Re z->-infinity, and A(z)=O(exp(-Re z)) uniformly up to either bank as Re z->infinity. The latter follows directly by the standard large-t expansions of asin(t/2) and t/sqrt(4-t^2) on the two half-planes, with their boundary limits; their product has real part -3 log|t|+O(1).

Let Y_K=(2K+1)pi and deform a small positively oriented Cauchy circle about zero into the rectangle with horizontal sides at +-Y_K, slit along the finitely many cuts zeta_k+[0,infinity), |k|<=K, and with radius-r endpoint circles. Send both vertical sides to infinity. Their integrals vanish by the preceding bounds. The boundary orientation is worth stating: the positively oriented boundary of the slit rectangle has its external rectangle counterclockwise and each slit boundary clockwise, with the analytic domain to the left. Each slit boundary runs lower bank inward, clockwise endpoint circle, upper bank outward, exactly as in H_k. Applying the residue theorem to A(z)z^(-n-1) gives the coefficient as the external-rectangle integral plus these clockwise cut contributions. Hence

[z^n]A(z) = sum_{|k|<=K} H_k(n) + E_K(n),
|E_K(n)| <= M/(pi Y_K^(n+1)).

Consequently

[z^n]A(z) = sum_{k in Z} H_k(n),  n>=1.

For absolute convergence, periodicity leaves only two translated endpoint-circle branches. Thus there is a finite M_r with |A|<=M_r on all radius-r circles. Since Re zeta_k=rho>0,

|zeta_k+x|>=|zeta_k| for x>=0,
|z|>=|zeta_k|-r on C_k(r).

The circle length and the L1 bank bounds therefore give, uniformly in k and n>=1,

|H_k(n)| <= C_r (|zeta_k|-r)^(-n-1).

The sum converges absolutely because |zeta_k| is asymptotic to 2 pi |k|. Conjugation gives H_{-k}(n)=conj H_k(n); in particular H_0(n) is real.

## 5. Isolating the first flat pair

For any fixed R with |zeta_1|<R<|zeta_2|, choose the preceding r also so small that r<|zeta_2|-R. Then, for n>=1,

sum_{|k|>=2}|H_k(n)| <= C_R R^(-n).

For example, factor R^(-n) and use (R/(|zeta_k|-r))^n <= R/(|zeta_k|-r), leaving a convergent inverse-square sum. Therefore the exact normalization

[z^n]A(z) = H_0(n)+2 Re H_1(n)+O_R(R^(-n))

is valid. H_0 is defined by a full-cut integral, not by any finite or purely formal dominant Poincare expansion. That exact normalization is essential to a meaningful exponentially small claim.

## 6. Complex saddle on the original horizontal-cut circle

Fix k. Set zeta=zeta_k, g=g_k, phi=arg zeta, and

kappa = (g^2 pi^2/(4 zeta))^(1/3),
C_k = exp(zeta/2-3) sqrt(kappa/(3 pi)),

using principal roots. Since |phi|<pi/2, arg kappa=-phi/3 and Re kappa>0.

Choose

r_n = |(g pi zeta/(2n))^(2/3)|,
delta_s = zeta kappa n^(-2/3) = r_n exp(2 i phi/3).

On the original endpoint circle delta=r_n exp(i alpha), -pi<=alpha<=pi, the exponent after removing zeta^(-n-1) and its constant is

n delta/zeta + g pi/sqrt(delta) + O(n^(-1/3)),

uniformly in alpha. Its leading real part is

|kappa| n^(1/3) f_phi(alpha),
f_phi(alpha)=cos(alpha-phi)+2 cos(alpha/2).

The derivative factors as

f_phi'(alpha)=-2 sin(3 alpha/4-phi/2) cos(alpha/4-phi/2).

For |phi|<pi/2 and -pi<=alpha<=pi, the cosine is positive and the sine argument lies strictly between -pi and pi. The sole stationary point alpha_s=2phi/3 is thus the unique global maximum. Its value is 3 cos(phi/3). This selects the principal complex saddle without rotating any cut.

Writing alpha=alpha_s+theta, the full leading complex phase is

kappa n^(1/3)[exp(i theta)+2 exp(-i theta/2)],

whose second derivative at zero is -(3/2)kappa n^(1/3). Since Re kappa>0, the original real-theta contour is a valid complex Gaussian descent contour. Outside |theta|<=n^(-1/6+eta), for fixed sufficiently small eta>0, there is relative loss exp(-c n^(2eta)); a fixed angular distance has loss exp(-c n^(1/3)).

The two banks with x>=r_n are negligible. Their moduli are B_cut(x), and

integral_{r_n}^infinity B_cut(x)|zeta+x|^(-n-1) dx
 <= const |zeta+r_n|^(-n-1)
 = O(|zeta|^(-n-1) exp[-|kappa|cos(phi)n^(1/3)+O(n^(-1/3))]).

This is exponentially smaller than the saddle envelope, whose exponential factor is exp(3 Re kappa n^(1/3)).

The clockwise circle sign gives the exact parametrized contribution

(1/(2 pi)) integral_{-pi}^pi
 r_n exp(i alpha) A(zeta-r_n exp(i alpha))
 (zeta-r_n exp(i alpha))^(-n-1) d alpha.

Its leading Gaussian evaluation is

H_k(n) ~ C_k zeta_k^(-n) exp(3 kappa_k n^(1/3)) n^(-5/6).

In particular, the odd-sector amplitude includes the negative sign exp(zeta_k/2)=2(-1)^k.

## 7. Direct all-orders coefficient algorithm on the same circle

This formulation avoids even a local contour rotation. Put h=n^(-1/6), alpha=alpha_s+h y, and

u(h,y)=kappa h^4 exp(i h y),
Tloc(u)=zeta(1-u)/2 + g pi/sqrt(exp(zeta u)-1)
        -3 atan(sqrt(exp(zeta u)-1))/sqrt(exp(zeta u)-1).

Define the formal series

S(h,y)=Tloc(u(h,y))-(h^(-6)+1)log(1-u(h,y))
       -3 kappa h^(-2)-(zeta/2-3)
       +(3 kappa/4)y^2+i h y.

All negative powers and the constant term cancel, so S belongs to h C[y][[h]]. The coefficient of h^j has the parity of j as a polynomial in y. The added i h y is the circle Jacobian exp(i h y).

For every j>=0 set

c_{k,j}=sqrt(3 kappa/(4 pi)) integral_R
 exp(-3 kappa y^2/4) [h^(2j)]exp(S(h,y)) dy.

Only finitely many Taylor coefficients are used for any fixed j. These absolutely convergent complex Gaussian moments are evaluated algebraically by

E(y^(2m))=(2m-1)!! [2/(3 kappa)]^m,
E(y^(2m+1))=0.

The square root is principal, so the normalized zeroth moment is 1. Thus c_{k,0}=1.

The first terms are

S(h,y)=i(y-kappa y^3/8)h
 +[kappa^2(1-zeta)/2+3 kappa y^4/64]h^2+O(h^3).

Consequently

c_{k,1}=kappa^2(1-zeta)/2-5/(36 kappa).

For every fixed K>=0 and fixed k,

H_k(n)=C_k zeta_k^(-n) exp(3 kappa_k n^(1/3)) n^(-5/6)
 [sum_{j=0}^K c_{k,j}n^(-j/3)+O_{k,K}(n^(-(K+1)/3))].

To justify the all-orders remainder, use the symmetric central window |y|<=h^(-eta) for a small fixed eta>0. The convergent local formula and the exponential have Taylor remainders, at every finite order J, bounded by h^(J+1) times a polynomial in |y| times exp(C h(1+|y|^3)). Because h|y| tends to zero and Re kappa>0, multiplication by the complex Gaussian is bounded by a fixed integrable Gaussian times that polynomial. Expand through order 2K+1. Odd terms integrate to zero on the symmetric window; extending the polynomial-Gaussian integrals to R costs less than every power of h. The angular minor-arc estimate controls its complement and the preceding bank bound controls both lips. Thus the integrated error is O(h^(2K+2)), as claimed. The prefactor is kappa h^5/(2 pi), multiplied by sqrt(4 pi/(3 kappa)), giving sqrt(kappa/(3 pi)) h^5.

The coefficients agree with the delivered dominant expansion at k=0, because both are all-orders asymptotic expansions of the same exact H_0 and the remainder sum over k!=0 is exponentially smaller than the dominant envelope.

## 8. Fully quantified first-pair statement

Let

E_1(n)=|zeta_1|^(-n) exp(3 Re(kappa_1)n^(1/3))n^(-5/6).

For any fixed K>=0 and |zeta_1|<R<|zeta_2|,

[z^n]A(z)-H_0(n)
 =2 Re{C_1 zeta_1^(-n) exp(3 kappa_1 n^(1/3))n^(-5/6)
         sum_{j=0}^K c_{1,j}n^(-j/3)}
  +O_K(E_1(n)n^(-(K+1)/3))+O_R(R^(-n)).

The error is an absolute envelope statement. It does not claim an equivalent for the real oscillatory pair at indices where cancellation makes that pair small.

For reference,

|zeta_1|=6.4343010234236197238...,
|zeta_2|=12.642605841878585736...,
kappa_1=1.0378535337826070537...-0.50289435373455356015... i,
C_1=-0.033949227189151398227...+0.0077918187901695837193... i,
c_{1,1}=-3.5469635061184515587...-2.4403131696621088141... i.

Here [z^n]A(z)=a_n/n! in the normalization of the frozen source.
