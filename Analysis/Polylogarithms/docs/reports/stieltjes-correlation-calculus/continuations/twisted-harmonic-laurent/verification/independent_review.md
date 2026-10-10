# Independent mathematical review

Reviewed against ProveIt snapshot `e0d9463bdee9685dfb1dddb819059cc738540c57`.
This note records an independent derivation of the distributional core,
checks of its normalization, and the confirmed source corrections. It
does not claim formal verification or numerical independence of periods.

## 1. Entire Fourier family and the Hurwitz continuation

Use the circle T = R/Z, Fourier coefficient
`hat(f)(n) = <f, exp(-2*pi*i*n*x)>`, and `Delta = delta_0 - 1`.
For `n != 0`, set

```
lambda_n = log(2*pi*abs(n)) + i*pi*sgn(n)/2,
hat(W_s)(n) = exp((s-1)*lambda_n),
hat(W_s)(0) = 0.
```

On every compact set of spectral parameters, these Fourier coefficients
and every spectral derivative have a common polynomial growth bound in
`n`. Pairing with the rapidly decreasing Fourier coefficients of a smooth
test function therefore gives a normally convergent holomorphic series.
Thus `W_s` is an entire distribution-valued family. The Hurwitz Fourier
formula identifies

```
Z_s = Gamma(1-s) W_s
```

with the ordinary integrable function `zeta(s,x)` for `Re(s)<1`.
It suffices first to use the absolutely convergent Fourier formula for
`Re(s)<0`; both sides are holomorphic as distributions on `Re(s)<1`,
so analytic continuation gives the remaining strip.

The classical analytic inputs are the Hurwitz Fourier formula and shift
identity, DLMF 25.11.9 and 25.11.3:

- https://dlmf.nist.gov/25.11.E9
- https://dlmf.nist.gov/25.11.E3

At `s=1`, `W_1=Delta`, hence `Res(Z_s)=-Delta`.
At `s=k+1`, `k>=1`, `W_(k+1)=delta_0^(k)`, hence

```
Res_(s=k+1) Z_s = (-1)^(k+1) delta_0^(k)/k!.
```

There is no contradiction with the ordinary Hurwitz pole of residue one
at `s=1`: restricting `-Delta = 1-delta_0` to the open interval `(0,1)`
leaves the constant function one. For `k>=1`, the extra spectral poles
are supported only at the endpoint.

## 2. Laurent coefficients are concrete cutoff finite parts

Write

```
Z_(1+w) = -Delta/w + sum_(j>=0) (-1)^j T_j w^j/j!.
```

The shift formula implies
`gamma_j(x) = log(x)^j/x + gamma_j(1+x)`.
Thus, for a smooth periodic test function `phi`,

```
<T_j,phi> = lim_(eps->0+)
  [integral_eps^1 gamma_j(x) phi(x) dx
   + phi(0) log(eps)^(j+1)/(j+1)].
```

Only the value `phi(0)` needs subtraction because
`(phi(x)-phi(0))*log(x)^j/x` is integrable. The mean is zero, either
from the zero Fourier coefficient or from the Hurwitz antiderivative.
This independently confirms that the spectral Laurent coefficients and
the claimed elementary cutoff convention agree.

For `k>=1` put `c_k=(-1)^(k+1) k!` and
`P_k = c_k FP_(s=k+1) Z_s`; put `P_0=-T_0`. The corresponding raw
Hadamard cutoff convention is, for `k>=1`,

```
<P_k,phi> = lim_(eps->0+)
 [integral_eps^1 psi^(k)(x) phi(x) dx
  + c_k sum_(j=0)^(k-1)
       phi^(j)(0) eps^(j-k)/(j!*(j-k))
  + c_k phi^(k)(0) log(eps)/k!].
```

For `k=0` it is
`<P_0,phi> = lim [integral_eps^1 psi(x)phi(x)dx - phi(0)log(eps)]`.

To derive this directly, subtract the Taylor polynomial of `phi` of
degree `k` in the singular term `x^(-k-1-w)`. The analytic integrals of
its monomials are `1/(j-k-w)`; their constant terms for `j<k` and their
pole for `j=k` give exactly the displayed subtractions. The remaining
term `zeta(k+1,1+x)` is smooth at the endpoint. This also proves that no
unrecorded local counterterm occurs in `P_k`.

## 3. Harmonic endpoint correction

The local gamma expansion is

```
Gamma(-k-w) = (-1)^(k+1)/(k!*w)
               + (-1)^k (H_k-gamma)/k! + O(w).
```

Multiplying by `(2*pi*i*n)^(k+w)` gives, for nonzero `n`,

```
hat(P_k)(n) = (2*pi*i*n)^k * (gamma + lambda_n - H_k),
hat(P_k)(0) = 0.
```

Therefore the derivative-compatible family is exactly

```
Q_k = D^k P_0 = P_k + H_k delta_0^(k)       (k>=1).
```

At `k=1`, direct integration by parts provides a useful independent
sign check: `D P_0 = P_1 + delta_0'`. The extra term evaluates as
`-phi'(0)`, agreeing with the expansion of
`psi(eps)phi(eps)` at the lower endpoint. This tests the sign without
using the gamma Fourier expansion.

## 4. Quadratic convolutions and all endpoint constants

All distributions on the compact circle can be convolved. One may
define convolution as the pushforward of their tensor product under
addition; equivalently Fourier coefficients multiply. No pointwise
product of singular distributions is being used.

Set `A_n=gamma+lambda_n`. Expansion at `s=1` gives

```
hat(T_0)(n) = -A_n,
hat(T_1)(n) = (A_n^2+zeta(2))/2,       n!=0.
```

Consequently

```
P_0 * P_0 = 2 T_1 - zeta(2) Delta,
P_0 * check(P_0) = T_1 + check(T_1) + 2 zeta(2) Delta.
```

For the reflected identity, the independent calculation is
`A_n = a + i*pi*sgn(n)/2`, with real `a=gamma+log(2*pi*abs(n))`.
Then `A_n*A_(-n)=a^2+pi^2/4`, while
`hat(T_1)(n)+hat(T_1)(-n)=a^2-pi^2/4+zeta(2)`.
The difference is `pi^2/3=2*zeta(2)`, fixing the endpoint coefficient.
The zero Fourier mode on each side is zero because `hat(Delta)(0)=0`.
Replacing `Delta` by `delta_0` would fail this check.

For all `k,l>=0` the same exact polynomial calculation gives

```
P_k * P_l = D^(k+l)
 [2 T_1 + (H_k+H_l) T_0 + (H_k*H_l-zeta(2)) Delta],

P_k * check(P_l) = (-1)^l D^(k+l)
 [T_1 + check(T_1) + H_l T_0 + H_k check(T_0)
  + (H_k*H_l+2*zeta(2)) Delta].
```

The factor `(-1)^l` is required because reflection reverses the sign of
each derivative. The positions of `H_l*T_0` and `H_k*check(T_0)` are
also fixed by direct multiplication and must not be interchanged.

## 5. Uniqueness is relative to a stated normalization

Meromorphic continuation from the open half-plane `Re(s)<1` uniquely
determines `Z_s`, and hence all its Laurent coefficients and finite
parts. The explicit cutoff formulas above fix the same extension.
Fourier coefficients uniquely determine a distribution on the circle.

In contrast, agreement with `psi^(k)(x)` for `0<x<1` and mean zero
alone is not a uniqueness theorem for higher endpoint extensions:
one can add `delta_0'`, or other delta derivatives, without changing
either property. No proof in the article should replace the spectral
or cutoff normalization by those weaker conditions.

## 6. Confirmed source corrections

### Arctanh branch

Pinned `chapters/03-algebraic.tex`, lines 196-211, equation
`cleo:eq:lintanh`, uses `theta*log(tan(theta/2))` with
`theta=arcsin(lambda)` in a real `abs(lambda)<1` discussion.
For negative lambda, principal `log` contributes `i*pi*theta`.
At `lambda=-1/2` this is exactly `-i*pi^2/6`.

An independent 65-digit quadrature gave

```
LHS = -0.5317299165586139653837501727942413752855676479502779988
printed RHS = LHS - 1.644934066848226436472415166646025189218949901206798438 i
```

The corrected expression uses `log(abs(tan(theta/2)))`, with its
continuous value zero at lambda zero. Its residual in this check was
about `1.2e-66`. The proof is derivative equality
`d/dtheta F(sin(theta))=theta/sin(theta)` and the common zero value
at the origin; the numerical check is not its justification.

### Unsupported non-elementarity wording

Pinned `chapters/03-algebraic.tex`, line 194, describes the diagonal
`pi*chi_2(3-2*sqrt(2))` as non-elementary. No comparison algebra or
nonreduction theorem is supplied. The proposed patch preserves its
exact integral evaluation and replaces the unsupported adjective by
the accurate status statement. This does not assert that the value
has an elementary reduction.

### Coefficient field clarification, not a patched false theorem

Pinned `chapters/07-integration.tex`, lines 248-254, discusses a
quadratic-character example before mentioning `Q(sqrt(q))`. That
field description is valid for that example and should be scoped to
it. General additive or character coordinates require their own
algebraic fields. For example, the primitive character mod 5 with
`chi(2)=i` already has values outside the real field `Q(sqrt(5))`.
This issue is recorded as an editorial clarification, and the minimal
patch does not modify this paragraph.

## 7. Bell coefficients and the ordinary convergent identities

The regularized germ `B(u)=-u Z_(1+u)` has nonzero Fourier
coefficient `Gamma(1-u)*exp(u*lambda_n)`. Its logarithm is therefore

```
u*(gamma+lambda_n) + sum_(r>=2) zeta(r)*u^r/r.
```

Comparison with
`B(u)=Delta+sum_(r>=1) (-1)^r T_(r-1)*u^r/(r-1)!`
proves the stated convolution Bell polynomial with prefactor
`(-1)^(n+1)/(n+1)`. The factor is independently fixed by
`n!/(n+1)!`; no factorial is absorbed into the definition of `T_n`.
Pairing with a smooth test function justifies analytic convergence on
every closed disk of radius less than one: the gamma factor is bounded
there, and the exponential in `lambda_n` has polynomial growth in `n`.

The products `T_0*T_1`, `T_0*T_2`, and `T_1*T_1` were independently
checked as polynomials in `A=gamma+lambda_n`, using

```
T_0: -A,
T_1: (A^2+zeta(2))/2,
T_2: -(A^3+3*zeta(2)*A+2*zeta(3))/3,
T_3: (A^4+6*zeta(2)*A^2+8*zeta(3)*A
      +3*zeta(2)^2+6*zeta(4))/4.
```

All three stated identities agree, including the less immediate
constant `-zeta(4)/4` in `T_1*T_1`. This last simplification uses
`zeta(2)^2=5*zeta(4)/2`. Zero modes agree because all scalar constants
in this convolution algebra multiply `Delta`.

For the displayed ordinary integral `I_(m,n)(a)`, the two singular
factors have separated singular supports when `0<a<1`. A partition of
unity permits their product because near either singular support the
other factor is smooth. The cutoff formula is exactly

```
lim_(eps->0+) [
 integral_eps^(a-eps) gamma_m(x)*gamma_n(a-x) dx
 + integral_a^1 gamma_m(x)*gamma_n(1+a-x) dx
 + gamma_n(a)*log(eps)^(m+1)/(m+1)
 + gamma_m(a)*log(eps)^(n+1)/(n+1)].
```

Subtracting `gamma_n(a)*log(x)^m/x` and its counterpart at `x=a`
leaves an absolutely integrable function. Integrating the subtraction
terms gives exactly the two positive `log(a)` terms in the article.
The discarded boundary intervals have size
`O(eps*(1+abs(log(eps))^M))`, uniformly for `a` in compact subsets
of `(0,1)`, so this operation adds no hidden constant. Restricting
`Delta` to `(0,1)` gives the constant `-1`; this independently checks
the signs of all four ordinary integral formulas.

The half-shift specialization uses
`gamma_1(1/2)=gamma_1-2*gamma*log(2)-log(2)^2`.
It follows by expansion of `zeta(s,1/2)=(2^s-1)*zeta(s)` at `s=1`.
In particular the coefficient of the unshifted `gamma_1` is one.

## 8. Repeated primitive normalization and Gamma convolution

On zero-mean periodic distributions, multiplication of the nonzero
Fourier modes by `(2*pi*i*n)^(-q)` fixes the primitive and its constant
uniquely. The generating identity is

```
D^(-q) Z_(1+w) = Z_(1-q+w)/(-w)_q,
1/(-w)_q = -1/((q-1)!*w)
              * product_(r=1)^(q-1) (1-w/r)^(-1).
```

Coefficient extraction gives exactly

```
D^(-q) T_n(x) = (-1)^(n+1)*n!/(q-1)!
 * sum_(j=0)^(n+1) h_(n+1-j)^(q-1)*zeta^[j](1-q,x)/j!.
```

The pole coefficient also agrees: it is
`-zeta(1-q,x)/(q-1)!`, the ordinary representative of
`-D^(-q)Delta`. Thus it is not permissible to drop that coefficient
and then supply an arbitrary integration constant. Every Hurwitz jet
on the right has mean zero, by differentiating the integrable Hurwitz
family on `Re(s)<1`, so the displayed representative has the required
normalization.

For `q=1` the endpoint terms are powers of `log(x)` and are locally
integrable. For `q>=2` the shift formula gives singular endpoint terms
`x^(q-1)*log(x)^j`; these vanish at zero and have matching periodic
limits through derivative order `q-2`. This verifies the stated
continuity, and in fact gives at least `C^(q-2)` regularity. The next
derivative generally contains a logarithm, so continuity cannot be
extended without a separate cancellation argument.

The `P_k` and `Q_k` primitive formulas were separately derived by
differentiating the gamma prefactor at `1-p`, where `p=q-k>0`.
Since `psi(p)=H_(p-1)-gamma`, the numerator coefficients are exactly
`H_(p-1)-H_k` for `P_k` and `H_(p-1)` for `Q_k`.
The cases `D^(-1)T_0=-zeta'(0,x)` and
`D^(-1)T_1=zeta''(0,x)/2` provide direct first-primitive sign checks.

Finally `Dg=P_0`, with `g=log(Gamma)-log(2*pi)/2`, implies
`g*g=D^(-2)(P_0*P_0)`. Substituting the just-verified primitive
formula gives

```
(g*g)(a) = zeta''(-1,a)+2*zeta'(-1,a)
                         +(2-zeta(2))*zeta(-1,a).
```

This is the ordinary split integral displayed in the article. The
integral is convergent because its only endpoint singularities are
logarithmic; at `a=1` the product is still integrable. Its constant is
fixed by the zero mean on both sides. The reflected correlation has
the separate minus sign `-D^2(g*check(g))=P_0*check(P_0)`, also
confirmed independently.

## 9. Independent review of the shifted harmonic Laurent theorem

The section `04_harmonic_laurent.tex` was read in full. The following
derivations independently verify its core statements and the places
where interchange of operations could otherwise lose a finite term.

### 9.1. Generating family and the beta normalization

The coefficient of `u^r` in
`Gamma(n+u)/(Gamma(n)*Gamma(1+u))` is the strict elementary harmonic
sum `e_r(n-1)`, because the gamma quotient is the finite polynomial
`product_(j=1)^(n-1)(1+u/j)`. Summing these polynomials with an
auxiliary variable gives `x/(1-x)^(1+u)`. It follows that

```
Gamma(s)*F(s,u;a)
 = integral_0^infinity t^(s-1)*exp(-(a+1)*t)
                         *(1-exp(-t))^(-1-u) dt.
```

At `s=1`, initially `Re(u)<0`, the beta integral is
`F(1,u;a)=B(a+1,-u)=-R_a(u)/u`. Its subtraction from the unshifted
value `-1/u` therefore produces `(R_a(u)-1)/u`, with positive sign.
This fixes both the primitive identity and the factor
`(-1)^p/(p-1)!` in the positive integer evaluation. Differentiating
the logarithm of `R_a` gives the complete harmonic polynomials with
plus signs; the numerator coefficients `e_r` retain the elementary
minus-sign convention. These two different families must not be
interchanged.

The rational-grid projection factor was checked directly. The change
of variables `m_0=q(n-1)+h`, `m_i=q*k_i` contributes `q^(p+r)`
to `E_r`, whereas the `r+1` Fourier filters contribute `q^(r+1)`
to the displayed sum of colored polylogarithms. Their ratio is
`q^(1-p)`, exactly as stated. The endpoint case `h=q` remains valid:
the strict ordering of the inner multiples of `q` is then
`k_i<=n-1`.

The degree-three odd-denominator example was independently reduced
using `H=-2*log(2)`, `H^(2)=-2*zeta(2)`, `H^(3)=-6*zeta(3)`,
and `Z_k=(2^k-1)*zeta(k)`. The coefficient is

```
E_3(2;-1/2)
 = 31*zeta(5)-13*zeta(2)*zeta(3)-15*log(2)*zeta(4)
   +14*log(2)^2*zeta(3)-4*log(2)^3*zeta(2).
```

Multiplication by `3!/4=3/2` converts `e_3` to the cubic harmonic
numerator and `(n-1/2)^2` to the odd denominator. This verifies the
displayed nonlinear identity without an integer-relation fit.

### 9.2. A moving pole and the zero of reciprocal gamma

Factoring the Mellin integrand as

```
t^(s-2-u)*phi(t,u,a),
phi=exp(-(a+1)*t)*(t/(1-exp(-t)))^(1+u)
   = sum_(k>=0) b_k(u,a)*t^k
```

gives the polar terms `b_k(u,a)/(s-1-u+k)`. The analytic branch of
`phi` at zero has value one. Taylor subtraction on `0<t<1`, with
the exponentially convergent integral on `t>1`, leaves a jointly
holomorphic remainder in `Re(s)>1+Re(u)-K`. Compact shift sets in
`Re(a)>-1` give a uniform positive exponential decay rate at infinity.
Parameter derivatives add powers of `log(t)` at zero and polynomial
factors at infinity, which do not change the relevant integrability.
These facts justify coefficient extraction with a common local
parameter domain.

At `s=-m+eps`, exactly the index `k=m+1` is singular near `u=0`.
Consequently

```
F(-m+eps,u;a)
 = b_(m+1)(u,a)/[Gamma(-m+eps)*(eps-u)]
   + Q_m(eps,u;a)/Gamma(-m+eps),
```

with `Q_m` jointly holomorphic. The second summand is `O(eps)` even
after any fixed `u`-coefficient is extracted, because
`1/Gamma(-m+eps)` has a simple zero independent of `u`. Thus the
analytic remainder contributes neither a negative power nor the
constant Laurent coefficient. It may contribute to every later
coefficient, so the finite-polynomial conclusion cannot be extended
to spectral derivatives by this argument.

Write `b_(m+1)=sum_j b_j*u^j` and
`1/Gamma(-m+eps)=sum_(ell>=1) g_ell*eps^ell`. Expanding
`1/(eps-u)` first as a germ in `u` yields

```
[u^r] b_(m+1)(u,a)/(eps-u)
 = sum_(j=0)^r b_j*eps^(-r+j-1).
```

Its coefficient at `eps^(-h)`, after multiplying by reciprocal
gamma, is `sum_(j=0)^(r-h) b_j*g_(r+1-h-j)`. This is exactly

```
[u^(r+1-h)] b_(m+1)(u,a)/Gamma(u-m),   0<=h<=r.
```

This verifies the claimed rule including `h=0`, where a missing
gamma Taylor coefficient would change the finite part. The leading
coefficient follows from
`b_(m+1)(0,a)=B_(m+1)(-a)/(m+1)!` and
`g_1=(-1)^m*m!`; Bernoulli reflection makes their product
`-B_(m+1)(a+1)/(m+1)=zeta(-m,a+1)`. Thus the cancellation rule
at zeros of the Hurwitz value is correct.

The order of operations is essential. At a fixed nonzero small `u`,
putting `s=-m` first usually gives zero from reciprocal gamma.
Differentiating that value in `u` cannot recover the Laurent data at
the intersection of the moving divisor. Already `r=m=0` would lose
the known value `zeta(0,a+1)=-a-1/2`. The article explicitly avoids
this interchange.

### 9.3. Principal pole and differentiation of the finite part

Near `(s,u)=(1,0)`, the numerator of the simple moving pole can be
replaced by `C(u)=1/Gamma(1+u)`: the difference
`(1/Gamma(s)-C(u))/(s-1-u)` is jointly holomorphic by the analytic
divided-difference formula. For `a=0`, the identity
`F(1,u;0)=-1/u` then fixes the holomorphic remainder at `s=1` as
`(C(u)-1)/u`. Its coefficient is `c_(r+1)`. Subtracting the shifted
Dirichlet series is normally convergent for `Re(s)>0`, and its value
at one is `-h_(r+1)(a)`. Therefore both the full principal part and
the finite part at `s=1` agree with the section.

The finite-part differentiation identity admits a second check not
using Laurent multiplication. From the defining generating series,
`partial_a b_(m+1)=-b_m`, so for `m>=1`

```
partial_a A_m(u,a) = (m-u)*A_(m-1)(u,a),
A_m(u,a)=b_(m+1)(u,a)/Gamma(u-m).
```

Taking `u^(r+1)` gives
`C_(m,r)'=m*C_(m-1,r)-R_(m-1,r)`, since the residue is the
coefficient `u^r`. At `m=0`, differentiating
`(u/2-a-1/2)/Gamma(u)` gives `-u/Gamma(1+u)`, whose coefficient
is `-c_r`. This checks the residue correction and its sign entirely
within the finite polynomial calculus.

Finally, the higher Stieltjes differentiation formula uses
`(1+eps)_k=k!*product_(j=1)^k(1+eps/j)`. Comparing coefficients
after `partial_a^k E_r(s;a)=(-1)^k(s)_k E_r(s+k;a)` gives exactly
the stated factor `(-1)^(ell+k)*k!*ell!`, the elementary
coefficient `e_i(k)`, and division by `j!` on the spectral derivative.
The principal part at one is independent of `a`, so no derivative
of a pole term is omitted in that calculation.

No mathematical error was found in the reviewed harmonic section.
The attribution caveat remains material: the beta method and
unshifted height-one theory have prior literature, and these exact
checks establish validity, not priority.

## 10. Independent review of the polylogarithm realization

The full section `05_polylogarithms.tex` was reviewed. For a positive
Fourier index `n`, the mixed coefficient is

```
(2*pi*n)^(alpha+beta)*exp(i*pi*(alpha-beta)/2).
```

For a negative index it has the opposite phase. Separately summing
these two half-series in `Re(alpha+beta)<-1` gives exactly the two
polylogarithms of order `-alpha-beta` in the section. Their phase
signs agree with the stated Fourier convention. Normal convergence
after pairing with a smooth test function proves the entire
distribution family, while the ordinary representatives on any
compact subinterval of `(0,1)` are identified by analytic
continuation. The integer specialization is
`N_(k,l)=(-1)^l*D^(k+l)Delta`, including its constant `-1` on the
open interval at `k=l=0`. Differentiation must precede specialization.

Each `alpha` derivative multiplies a Fourier coefficient by
`log(2*pi*i*n)` and each `beta` derivative by
`log(-2*pi*i*n)`. The mixed operator therefore gives
`hat(P_k)(n)*hat(P_l)(-n)` as claimed. The unreflected operator
is the exact product of the two linear polynomials in the same
logarithm. This separately verifies all harmonic terms and both
orientations.

To check the constants in the first-Stieltjes formulas, put
`c=gamma+log(2*pi)` and `d=pi/2`. On the positive-frequency term,
the reflected operator is
`(c+i*d-partial_s)*(c-i*d-partial_s)=(c-partial_s)^2+d^2`.
Using `Re(L_0)=-1/2`, the reflected convolution gives

```
gamma_1(h)+gamma_1(1-h)
 = 2*Re(L_2)-4*c*Re(L_1)-c^2+pi^2/12.
```

For the unreflected term, expansion of
`(c+i*d-partial_s)^2` gives

```
Re(L_2)-2*c*Re(L_1)+2*d*Im(L_1)
 -(c^2-d^2)/2-c*d*cot(pi*h).
```

This is `gamma_1(h)+zeta(2)/2`. Subtracting that last constant
leaves exactly `pi^2/24`; `2*d=pi` fixes the positive sign of
`pi*Im(L_1)`, and `c*d=pi*c/2` fixes the negative cotangent
term. Thus neither the sine phase nor the endpoint constant is lost.

Grouping `n=q*k+a` in the defining Dirichlet series proves the
rational-grid transform with coefficient `q^(-s)*z^a`, rather than
its complex conjugate. Differentiating its finite sum gives
`binom(j,v)*(-log(q))^(j-v)` as stated. At `s=1`, all Hurwitz
residues cancel because `sum_(a=1)^q z^a=0`; jets there require
expansion of the combined meromorphic germ before substitution.
The section already states this condition. No mathematical error
was found in these formulas.

## 11. In-repository provenance correction

Validity and novelty are separate audit questions. Later inspection
of the pinned tree, beyond the manuscript chapters and intake ledger,
found prior complete treatments under

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/`.

The following source matches were read directly:

- `convolution-algebra/article.tex`, `thm:Bell` and `eq:BellG`,
  prove the one-generator Stieltjes Bell algebra; `thm:product`
  and `eq:Gproduct` prove the bivariate Gamma multiplication law.
  The four low-order product and ordinary-integral examples agree
  exactly with the present formulas.
- The same file proves the contact correction and polygamma
  convolution collapse. Its `thm:reflected`, `eq:reflected`, is
  the present two-parameter polylogarithm kernel after negating
  its two spectral parameters, including the entire distributional
  continuation and arbitrary parameter derivatives.
- `convolution-calculus/Stieltjes_Convolution_Calculus.tex`,
  `eq:Li0identity`, is exactly the present symmetric
  first-Stieltjes formula in order-zero polylogarithm jets.
- `shifted-hurwitz-jets/sections.tex`, `shj:Uformula` and
  `shj:Ulemma`, already provide the complete repeated-primitive
  formula and the `C^(q-2)` periodic endpoint regularity. The
  same continuation provides canonical distributional residues,
  reflected all-index Stieltjes closure, and derivative contact laws.

Accordingly, the periodic and polylogarithmic foundation is a
consolidation with independent checking. It is not a new-to-repository
answer to a currently open question merely because an earlier intake
report listed the underlying normalization problem. The current
article's scope statements and audit section must credit these prior
continuations. This finding does not invalidate any formula, but it
materially changes the scientific status of the work.

The shifted harmonic Laurent theorem is a separate contribution
candidate. The present review verifies its proof, and the article
credits its beta and unshifted height-one antecedents. No exhaustive
priority claim is established for it either.

## 12. Harmonic coefficient symmetries and multiplication

The additional section `04b_harmonic_symmetries.tex` was read in full
and checked independently, without relying on the numerical case count.
The centered local kernel is an exponential times the even germ
`(t/(2*sinh(t/2)))^(1+u)`. It gives exactly

```
phi(t,u,-1-a)=phi(-t,u,a+u).
```

The shift on the right is `a+u`, not `a-u`. Its coefficient identity
and the fact that `A_m(u,a)` has no constant coefficient prove the
reflection formula with derivatives of lower depths and upper index
`j=r`. The fixed-depth Bernoulli reflection alone would fail already
at `m=r=1`.

The antiderivative rule follows from

```
partial_a^q A_(m+q)(u,a)
 = product_(nu=1)^q (m+nu-u)*A_m(u,a).
```

Its reciprocal has the complete harmonic coefficients in the section.
Because `A_(m+q)(0,a)=0`, coefficient extraction ends at depth `r`,
with no missing constant coefficient at `j=r+1`. Subtracting the
Taylor polynomial at the base point imposes all `q` initial conditions.

For multiplication, summing the `q` shifted local kernels gives
`q*phi(t/q,u,a)*exp(-u*Lambda_q(t))`. The negative sign in this
exponential and the coefficient scaling `q^(n-m)` were checked by
taking the ratio of the two defining kernels. Gamma recurrence then
produces `(u-m)_n*A_(m-n)`. The terminal term at `n=m+1` requires
`A_(-1)=1/Gamma(1+u)`; omitting it changes the positive-depth
corrections. The special case `q=2,m=1` has exactly the constant
correction `a/4+3/16` at depth one.

Finally, direct multiplication of the stated half-shift `b_2,b_3`
by `u(u-1)/Gamma(1+u)` and
`u(u-1)(u-2)/Gamma(1+u)` verifies all four half-shift Laurent
examples, including the canceled leading poles. No defect was found.

## 13. Independent derivation of the nonintegral-twist extension

This derivation was made before reading the twist section being
prepared by the other researcher. Its target is an explicitly open
question in the pinned source
`convolution-algebra/article.tex`, in the subsection
"Twists, characters, and alternate endpoint normalizations"
(lines 1105-1115): the all-index half-twist multiplication table with
its singular normalization and point-supported counterterms.
This question is distinct from the already-developed untwisted theory.

For real noninteger `theta`, retain every integer Fourier mode and set

```
lambda_n=2*pi*i*(n+theta),
hat(W_s^theta)(n)=lambda_n^(s-1),
D_theta=D+2*pi*i*theta.
```

The logarithm has argument `pi*sgn(n+theta)/2`. Compact parameter
sets give polynomial growth in `n`, so `W_s^theta` is entire as a
periodic distribution family. Every Fourier mode is present; the
convolution identity is `delta_0`, not `delta_0-1`. Its semigroup
law and covariant derivative are immediate mode by mode.

The ordinary representative of
`Z_s^theta=Gamma(1-s)*W_s^theta` is

```
exp(-2*pi*i*theta*x)*Phi(exp(-2*pi*i*theta),s,x),  0<x<1.
```

Here `Phi` is the Hurwitz--Lerch function. To prove this without
interchanging a conditionally convergent infinite sum, truncate its
defining series at `m=M`. The `n`th Fourier integral then combines
exactly to

```
integral_0^(M+1) t^(-s)*exp(-2*pi*i*(n+theta)*t) dt.
```

For `0<Re(s)<1`, the Lerch tail converges uniformly in `x` away
from its integrable `m=0` singularity, by summation by parts; its
partial exponential sums are bounded because the twist is nonintegral.
The oscillatory integral converges to
`Gamma(1-s)*lambda_n^(s-1)`. This proves the identification in an
open strip and hence by analytic continuation.

The local shift relation is

```
Z_s^theta(x)=exp(-2*pi*i*theta*x)*x^(-s)+Z_s^theta(x+1).
```

Taylor subtraction against a periodic test function yields all poles:

```
Res_(s=k+1) Z_s^theta
 = (-1)^(k+1)*D_theta^k delta_0/k!,    k>=0.
```

In particular the residue at one is `-delta_0`. There is no interior
residue because the Lerch function at a nontrivial unit twist is
entire in its order. This differs materially from the untwisted
Hurwitz residue `1-delta_0`.

Writing the regular coefficients at one as `T_n^theta` gives the
same cutoff subtraction `phi(0)*log(eps)^(n+1)/(n+1)` as before:
the extra local phase is `1+O(x)`. The Gamma-normalized germ has
the same exponential Bell coefficients as in the untwisted case.
Consequently all scalar multiplication coefficients remain ordinary
positive integer zeta values. What changes is the basis of functions,
now Lerch jets, and the unit, now `delta_0`.

The finite-part polygamma symbols are

```
hat(P_k^theta)(n)=lambda_n^k*(gamma+log(lambda_n)-H_k),
D_theta^k P_0^theta=P_k^theta+H_k*D_theta^k delta_0.
```

Thus all counterterms are completely explicit point-supported
distributions. The covariant delta derivative contains lower ordinary
delta derivatives through the binomial expansion of
`(D+2*pi*i*theta)^k`.

For a rational twist `theta=h/q`, the Lerch identity is

```
Phi(z,s,x)=q^(-s)*sum_(j=0)^(q-1) z^j*zeta(s,(x+j)/q),
z=exp(-2*pi*i*h/q).
```

The pole cancels in the finite sum. At the half twist this gives

```
T_n^(1/2)(x)=exp(-pi*i*x)*f_n(x),
f_n(x)=1/2*sum_(j=0)^n binom(n,j)*log(2)^(n-j)
       *[gamma_j(x/2)-gamma_j((x+1)/2)].
```

The low-order product is
`T_0^(1/2)*T_0^(1/2)=2*T_1^(1/2)-zeta(2)*delta_0`.
After removing the common phase, its ordinary representative is the
fully convergent identity

```
integral_0^a [f_0(x)*f_0(a-x)
             -f_0(a)*(1/x+1/(a-x))] dx
- integral_a^1 f_0(x)*f_0(1+a-x) dx
+ 2*f_0(a)*log(a)
=2*f_1(a),                              0<a<1.
```

The negative sign on the second integral is essential: wrapping the
second factor once around the circle adds the half-twist factor `-1`.
There is no ordinary constant `zeta(2)` on the right, because
`delta_0` restricts to zero on `(0,1)`.

At `a=1/2`, the identities

```
f_0(1/2)=pi/2,
2*f_1(1/2)=-4*beta'(1)-pi*log(2),
beta'(1)=pi/4*[gamma+2*log(2)+3*log(pi)-4*log(Gamma(1/4))]
```

give the exact ordinary Gamma/digamma integral value

```
pi*[4*log(Gamma(1/4))-gamma-3*log(2*pi)]
= -2.949191357491251847953447954349745088318971170849316403...
```

An independent direct quadrature at 55 decimal working digits agreed
with this value (rounded residual zero). To avoid endpoint loss of
precision, the first integral was doubled over `[0,a/2]` and its
integrand evaluated as

```
(f_0(a-x)-f_0(a))/x + g(x)*f_0(a-x)-f_0(a)/(a-x),
g(x)=[psi((x+1)/2)-psi(1+x/2)]/2,
```

using Gauss--Legendre quadrature. This check corroborates the proof;
it is not a replacement for the spectral or finite-part derivation.

There are two important orientation and limiting qualifications:

1. Bare reflection does not change `n+1/2` into its negative.
   The appropriate half-twist involution is
   `J U(x)=exp(-2*pi*i*x)*U(-x)`, with Fourier action
   `hat(JU)(n)=hat(U)(-n-1)`. It fixes `delta_0`, preserves
   convolution, and satisfies `D_(1/2)J=-J D_(1/2)`. Reflected
   closure formulas must use this involution, or pair opposite
   twists with ordinary reflection.
2. As `theta` tends to zero, the `n=0` mode must be removed first:
   subtract `Gamma(1-s)*(2*pi*i*theta)^(s-1)` times the constant
   function. The remaining Fourier family converges to the
   untwisted zero-mean Hurwitz family; its residue at one is then
   `1-delta_0`. The same removal must be made coefficientwise
   in Laurent or spectral jets. Omitting it creates a divergent
   logarithmic constant at the first Stieltjes level.

### Final audit of the saved twist section

After making the preceding derivation independently, the complete
saved section `03_twisted.tex` was read and checked. Its notation
uses `U_n^theta` for the twisted Laurent coefficients denoted by
`T_n^theta` in the derivation above. All central formulas agree.
The following additional checks concern material introduced in the
completed section:

- The rational polygamma representative has prefactor
  `q^(-k-1)` and the same colored phase as the rational Lerch
  sum. Its limiting case `k=0` is valid because the common
  Hurwitz pole cancels before the digamma finite part is taken.
- The all-index raw contact law follows by expanding the pole
  polynomial
  `-product_(j=1)^k(1+u/j)*D_theta^k(delta_0)/u`.
  Coefficientwise raw cutoff removes this term, whereas
  covariant distributional differentiation retains its regular
  polynomial coefficients. This yields the section's exact
  sign and factor `(-1)^n*n!` in `h_(k,n)`. The distinction is
  coefficientwise: treating the cutoff at a generic nonzero
  spectral parameter first would be a different operation.
- For the reflected table, put
  `A=gamma+log(lambda)`, `B=gamma+log(-lambda)`.
  Then `(A-B)^2=-pi^2=-6*zeta(2)`. Substitution of the Bell
  polynomials into both displayed reflected products reduces
  their differences to zero using this relation and
  `zeta(2)^2=5*zeta(4)/2`. This independently verifies the
  coefficients `1/2`, `1`, `7*zeta(4)/2`, and every sign.
  The generator has multiplier `exp(-i*pi*v*sgn(n+1/2))`,
  hence the stated positive coefficient of the Hilbert operator
  whose symbol is `-i*sgn(n+1/2)`.
- Multiplication by `(n+theta)^(-q)` gives primitive Fourier
  coefficients of order `abs(n)^(-q)*log(abs(n))^(N+1)`.
  Their first `q-2` ordinary derivatives are absolutely summable
  for `q>=2`, proving the stated periodic `C^(q-2)` regularity.
  The half-twist Gamma expression is the negative of the Lerch
  order derivative at zero, as required for a primitive of `U_0`.
- In the zero-mode subtraction theorem, all `n!=0` coefficients
  and their parameter derivatives have bounds uniform for
  `0<theta<=1/2`. Therefore smooth-test-function pairing permits
  both the limit and arbitrary fixed-order parameter
  differentiation. This supplies the needed control behind the
  coefficientwise limiting statement, not just pointwise mode
  convergence.

The cited literature distinction was also checked against the primary
papers. [Zhu, Hu, and Kim, arXiv:2505.10985v3](https://arxiv.org/pdf/2505.10985),
Theorem 1.13, gives the ordinary alternating Hurwitz convolution for
real `alpha,beta>1`; the statement does not specify the singular
periodic finite-part table proved here. [Hu and Kim,
arXiv:2106.14674](https://arxiv.org/pdf/2106.14674) defines the
modified Stieltjes constants with exactly the Taylor signs and
factorials used in the new section. Its Gamma-ratio order derivative
is also a classical input. Thus the special functions and the
nonsingular convolution are correctly credited, while the present
answer to the pinned open target concerns its singular normalization
and all-index contact terms. This is not a claim of exhaustive
global priority.

No mathematical defect was found in the saved twist section.

## 14. Limits of the present review

The review verifies the distributional construction, its endpoint
normalization, quadratic identities, Bell coefficients, ordinary
integral realizations, repeated primitives, and the shifted harmonic
Laurent and residue rules, and the mixed polylogarithm kernel by
separate derivations. The later report-level provenance inspection
identifies substantial pre-existing repository material as recorded
in Section 11 above. The nonintegral-twist extension was independently
derived before its written proof was inspected, and then audited as
recorded in Section 13; it addresses a separately identified open
target in the pinned report.
It does not prove the surviving S6 or S8 numerical candidates, rerun
the earlier S4 certificate, or claim a complete search for errors in
the entire repository. The current S2 and S4 proof statuses, the
surviving S6 and newer S8 conjecture statuses, and the rejection of a
different frozen S8 vector were checked directly in the pinned
manuscript chapters.
