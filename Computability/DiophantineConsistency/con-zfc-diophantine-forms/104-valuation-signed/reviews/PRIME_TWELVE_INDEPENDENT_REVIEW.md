# Independent mathematical review of the 215-operation twelve-integer construction

Reviewed 2026-10-24 UTC by a separate assistant worker from the construction
authors. This is an ordinary mathematical review, not external human peer
review, proof-assistant certification, or a newly encoded internal-ZFC proof.

## Objects and verdict

The reviewed builder is `research_input/integer_frontier/new12/build_prime12.py`,
with carrier `19`, rational auxiliary radicand, and default integer-root order.
Its emitted literal has twelve unrestricted integer variables, 215 live binary
operations, and exact total degree 2400. The mathematical equivalence uses the
full-residue interpolation theorem and signed native kernel proved in the
retained incoming `INTERPOLATION12.md`, with the same complete six-number
source-34 coefficient tuple. The changed construction passes this review.

The review independently checks the changed root-separation argument,
denominator clearing, all zero-multiplier boundaries, the new quintic,
integer main-congruence recovery, compatibility with the signed kernel,
completeness order, and the stated attained degree. It does not repeat the
entire inherited native-window compiler or the K215 runtime calibration.

## 1. The quintic actually needed

Use

    pi(x)=(x^2+3)(x^3-19)
         =x^5+3x^3-19x^2-57.

This polynomial is not monotone, and no monotonicity claim is needed.
Its quadratic factor has no real root; its cubic factor is irreducible over
Q by Eisenstein at 19. Consequently pi has no root in any real extension of
Q of degree at most two.

It has a root modulo every nonzero integer. For primes other than 3 and 19,
either `x^3-19` has a root modulo p, which is simple, or it is irreducible.
In the latter case its Frobenius permutation is a three-cycle and is even,
so its discriminant `-27*19^2=-3*(3*19)^2` is a nonzero square modulo p.
Thus `x^2+3` has a simple root. At p=19 the quadratic has the simple root
4. At p=2 the cubic has the simple root 1. At p=3 write x=1+3t; then

    ((1+3t)^3-19)/9 = t+3t^2+3t^3-2.

The polynomial on the right has derivative 1 modulo 3 and the root t=2
modulo 3, so Hensel lifting gives a 3-adic cube root of 19. Simple-root
lifting at the other primes and finite CRT prove intersectivity.

For `Dm=d^2` the builder's reduction is exact:

    A+B*d = ((u+d)^2+3H^2)((u+d)^3-19H^3).

All tuple assignments satisfy modulo 3

    q=2, X=2, a=Delta=H=0, u=1, Dm=1.

Therefore the odd coefficient B is 1 modulo 3. It never vanishes, even
though the new quintic is not monotone. This is the actual replacement
for the old positive-B argument.

## 2. Unconditional nonzero boundaries and realness

The affine choices `J=6j+1`, `W0=12w+4`, and `Y=(2v+1)q^3`, with the
actual large odd beta, force nonzero q,X,Y and sufficiently large absolute
values to give `Delta>1` and `H!=0`. Thus `Dm,Df,Dt` are positive for every
integer input. Put `I=s*r*c^2`, `Q=Delta^2 I^2`, and `delta=Q-1`.
Q is either zero or greater than one, so delta never vanishes.

If I=0, then S=I H^5=0, delta=-1, and the literal denominator-cleared
norm specializes to `(A^2-B^2 Dm)^16`. This cannot vanish: either value
`(u +/- sqrt(Dm))/H` lies in a real field of degree at most two, where
pi has no root. Hence any zero has I,S,s,r,c all nonzero.

For I nonzero, `|I|>=c^2`, `Df>|c|+1`, and
`V=Df*(c-R+4IT)-c` has `|V|>=1`: if its parenthesis is zero,
`|V|=|c|>=1`; otherwise `|V|>=Df-|c|>1`. Therefore
`Cy=Q V^2-1>0`, delta>0, and `Dy=Cy/delta>0`.

The only potentially negative radicand is Dg. If Dg<0, the guard radical
is the unique nonzero imaginary term in any conjugate factor, impossible
at a zero. Thus Dg>=0. Since s is nonzero,
`Dg=(3*Pair-4)s^2+1` implies Pair>0. The elementary joint-positivity
lemma now gives G>0 and eta*zeta>0. No guard is assumed before this
deduction.

## 3. Fixed-prime separation really covers every square class

Let `m=v_3(S)`. Because 3 divides H, m>=5. The four radicands
Dm,Df,Dt,Dy are nonzero 3-adic units, each congruent to 1 modulo 3.
The five roots used by the norm, in a convenient order, have valuations

    B*sqrt(Dm):       0,
    S*sqrt(Dy):       m,
    3S*sqrt(Df):      m+1,
    9S*sqrt(Dt):      m+2,
    27S*sqrt(Dg):     m+3+v_3(Dg)/2.

If Dg=0, discard the last zero term. If v_3(Dg) is odd, its square class
differs from the first four. If its valuation is even, its root valuation
is at least m+3. Within any common rational square class, every nonzero
term therefore has a distinct 3-adic valuation. Dividing by a chosen
radical representative gives rational coefficients with a unique least
valuation, so their sum cannot be zero. Character independence of distinct
rational square classes now forces every radical in a rational sum to be
rational. This argument does not assume independence of all square classes,
and does not merely test the complete signed sum.

Dm,Df,Dt,Dg have integer square roots once their roots are rational.
For Dy, rationality is followed by a separate integrality proof below.

## 4. Denominator clearing and adjacent-coefficient descent

The used norm routine is the polynomial

    delta^16 F32(Z;B^2 Dm,9S^2 Df,81S^2 Dt,729S^2 Dg,S^2 Cy/delta).

The five-root norm is of degree at most 16 in each squared radicand, so
this is an integer polynomial. The supplied routine is obtained by first
taking the three-root norm of the main, strong, and rational roots, with
delta^4 clearing, then two ordinary quadratic norms. The two additional
norms square the clearing factor twice, producing delta^16 exactly.
The nonvanishing of delta proved above licenses the rational interpretation
at every possible integer zero; clearing has introduced no zero-denominator
solutions.

If `y^2=Cy/delta`, then

    Q V^2-(Q-1)y^2=1.

For integral Q>1,V and rational y this implies y is integral. Write
`|y|=a/b` in lowest terms. Then `b^2 | Q-1`. For |V|>1, after making
V,y positive, use

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The first coordinate is integral. The reduced denominator of y' stays b,
since `2Q-1=1 mod b`. The norm is preserved, and `y>V` together with
`(Q-1)y<QV` gives `-V<V'<V`. The norm excludes V'=0. Descent reaches
|V|=1, where y=+/-1, so b=1. The |V|=1 case is immediate from the
original equation. Thus all five needed roots are integers.

## 5. Exact congruence and signed-kernel restoration

Absorb conjugate signs into the integral roots d,f,tau,g,y. The vanishing
factor yields

    S*n=A+B*d+S*(y+3f+9tau+27g),

so `I H^5 | A+B*d`. Let x=d-b0+HT. Then the latter numerator is

    Phi_H(x)=x^5+3H^2 x^3-19H^3 x^2-57H^5.

For any prime p with p^e exactly dividing H, if v_p(x)=b<e then the
leading x^5 term has valuation 5b and every other term has strictly
larger valuation. It cannot be divisible by p^(5e). Hence H divides x,
and gamma=(d-b0)/H is an integer. This remains valid at p=3 and p=19;
those coefficients can only increase the other terms' valuations.

Set rho=Delta I. The restored equations are

    d^2-Delta*c^2=1,
    f^2-Delta*I^2=1,
    rho^2*V^2-(rho^2-1)*y^2=1,
    d=X+a*c+gamma*H,
    tau^2-XY^2(XY^2+1)k^2=1.

The exposed auxiliary coordinates are actual integer polynomials:

    o=f*(c-R+4IT),
    j_aux=Delta*s^2*r^2*c^3*(c-R)+4*s*r*c*Df*T,
    V=f*o-c=c*j_aux-R.

Normalized Pell classification with c^2 dividing I gives p|m and
|c| dividing m (in fact p|c| divides m). Thus the inherited signed
auxiliary step-down needs no oddness of rho/c^2. The old expression
`(Delta*s*r-1)/2` must not be asserted integral. The signed-kernel route
instead gives p=R, R=2n_first-1, and X=sign(c)*2^R. The fixed residue
X=2 modulo 3 selects the positive orientation. The retained compiler
and syntactic-refutation calibration can then be applied on their stated
interface, exactly as in the interpolation parent.

## 6. Completeness remains noncircular

The same canonical native family gives the outer variables and integer
gamma. Choose the joint-positivity coordinate t and then nonzero guard
witness s. Apply the parent's full-residue interpolation lemma with N=s,
choosing I,f first with `4s c^2 | I`; set r=I/(s c^2). Intersectivity of
pi gives a residue a modulo this fixed I with pi(a+gamma)=0. The lemma
then supplies T=a modulo I and an integer auxiliary y. Therefore

    A+B*d=H^5*pi(T+gamma)

is divisible by S. Set

    n=(A+B*d)/S+y+3f+9tau+27g.

This integer makes one norm factor vanish. No positivity is demanded of n.
The order is outer data, t, s, I/f/r, an intersective residue, T/y, then n.
The corrected interpolation period is `4*n0*f`, not `4*n0`; the retained
proof also correctly makes I even and f odd before dividing by `4I f^2`.

## 7. Attained degree independently checked

The actual degrees are S=34, delta=32, Cy=82, center<=35. The integer
radicands have degrees 70,88,102,114; the numerator of the rational
radicand, `cn=S^2 Cy`, has degree 150. In the cleared norm the unique
top weighted contribution is cn^16. Every replacement of one factor of
cn by an integer radicand and a delta has lower degree, since
150>114+32 and 150>2*35+32. Thus the degree is 16*150=2400.

Write `a0=2^7 3^5 beta^4 j^4 w v`, `I0=s*r*c^2`, and
`b0=4I0*T-R0`. Then

    lead(cn)=2^20 a0^18 I0^8 b0^2,
    lead(P)=2^320 a0^288 I0^128 b0^32.

Selecting T^32 gives the nonzero coefficient

    [j^1152 w^288 v^288 s^160 r^160 c^320 T^32] P
      =2^2400 3^1440 beta^1152.

The exponents total 2400, and the coefficient remains positive after the
actual numeral specialization. This confirms the builder's exact degree
certificate, independently of generic gate-degree propagation.
