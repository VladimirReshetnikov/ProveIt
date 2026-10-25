# Reuse the product XY as the index carrier

Research note, 25 October 2026. New material prepared with AI assistance.

## 1. Result, scope, and exact formula

There are two principal ordinary polynomials in **ten strictly positive
integer unknowns**, with **76 operations / degree 626** and **77 operations /
degree 464**. Every operation is binary addition, subtraction, or multiplication;
fixed scalar products and squares count. All named quantities below are
polynomial abbreviations, not additional unknowns. The four fixed coefficients
are the entire directly indexed BFS943 compact44 tuple of the retained parent;
their literal bytes, hashes, and provenance are supplied. The ordinary theorem
is composed with the explicitly inherited native-to-refutation calibration.
It is not a new formal proof-assistant or encoded object-ZFC proof.

The inputs are `J,F,alpha,i,T,w,s,n,eta,zeta > 0`. Define

    q=beta*J+1, h=q-1, C=q-F-alpha, X=w*q, Y=q^3*s,
    D=X*Y, k=eta+zeta, c=k*Y+eta,
    A=D+Y+1, Delta=A^2-1, H=4*A-5,
    V0=D*Y, E=1+V0*(V0+1)*k^2,
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, B=(K0+w)*C-F,
    U=i*c^2, a=Delta*U^2*E, F0=1+a,
    G=E*F0, Fsq=1+4*a*F0, Q=Delta*(Fsq-1),
    b=c*T-R, V=Fsq*b-c, Kpos=X*(3*c-2*X)+2.

For the 76-operation polynomial use `L=V^2`; for the 77-operation polynomial
use `L=b*V`. Both use

    M=h*D*H,
    Z=h*D*[H*(n-L*B)+Kpos]-H*[D*B+h*e],
    RG=M^2*G,
    N=Q*(Z^2-RG*V^2)+(RG-Z^2).

The equation is `N=0`. The companion shifted equations replace `T` by
`T+alpha` in `b`, costing one additional addition, at the same degree.
They are provided as 77/626 and 78/464 companion circuits.

For proof only, put `delta=Q-1`, `Dy=Q*V^2-1`, `z=Z/M`,
`kappa=Kpos/H`, `rho=e/D`, `t=B/h`, and `W=1+h*L`. Then identically

    N=delta*Z^2-M^2*G*Dy,
    z=n+kappa-W*t-rho.                                  (1)

The divisibility theorem is the substantive change: the first-index recovery
needs only `q^4 | D`, not the former complete denominator `Y^2`. Here that is
automatic because `D=XY=w*q^4*s`. Moreover `XY` is useful twice more:
`A-1=XY+Y` and `V0=XY*Y`. Those three registers cost three operations,
replacing the four registers `X+1, Y(X+1), Y^2, XY^2`.

## 2. Product-square recovery without assuming signs of b and V

The fixed port box is `beta>=31` odd, `K0>0`, and
`0<MC<beta<MF<2beta`. Positive inputs give `q>=32`, `X>=q`, `Y>=q^3`,
`k>=2`, `c>=3`, `A>4`, `Delta>=3`, `U>=c^2`, `E>1`, `a>0`,
`Fsq>c+1`, `Q>1`, `D>2`, and `M>0`. Every integral `b` gives `V!=0`:
if `b=0` then `V=-c`; otherwise `|V|>=Fsq-c>1`. Thus `Dy>0`.

The identities

    Fsq=(1+2a)^2,  Q=4*Delta^2*U^2*G

imply `gcd(G,delta*Dy)=1`. At a zero, (1) gives `delta*z^2=G*Dy`.
Every prime dividing `G` has even valuation in `G`, because its valuations
in `delta,Dy` vanish and a rational square has even valuation. Therefore
`G=g^2` for some positive integer `g`. Since `F0=1 mod E`, its positive
factors are coprime, and hence `E=tau^2`, `F0=f0^2`, `g=tau*f0`.

The positive rational number `y=|z|/g` satisfies

    Q*V^2-(Q-1)*y^2=1.                                (2)

The retained adjacent-Pell descent gives integral `y`. For completeness,
write `y=r/m` in lowest terms. Then `m^2 | Q-1`. For `v=|V|>1`,
`v<y<Q*v/(Q-1)`, and the norm-preserving map

    v'=(2Q-1)*v-2*(Q-1)*y,
    y'=(2Q-1)*y-2Q*v

has nonzero integral first coordinate of absolute value below `v` and
preserves the reduced denominator `m` of the second coordinate. Descent
reaches `v=1,y=1`; hence `m=1`. Thus `z=epsilon*g*y` is an integer.

Set `f=1+2a` and `I=2U*g`. Then

    f^2=Fsq, f^2-Delta*I^2=1, Q=(Delta*I)^2, c^2 | I.   (3)

If `b=0`, equation (2) implies
`y^2-c^2=(c^2-1)/(Q-1)`, strictly between zero and one since
`Q>=9c^4>c^2`. This is impossible. Thus `b!=0`. Let `D0=Delta*U^2`.
Since `D0>=243` and `a=D0*E`,

    a^2/g^2=D0*a/(1+a)>D0/2>9.

In particular `a>3g` and `a>=c`. Consequently

    sign(V)=sign(b), |V|>=Fsq-c>a>3g, |V|>|b|,
    Fsq>2c, Fsq>g, y<(3/2)|V|.                       (4)

All these facts precede a sign assertion about `B,C,R,b,V`.

## 3. Folding, and a short exclusion of the third main index

The retained signed all-index folding theorem applies to (2),(3),
`c<=I`, `c^2|I`, and `V=-c mod f`. It gives
`c=psi_A(p)` with positive odd `p`. The first norm similarly gives
`k=2*psi_P0(n0)`, where `P0=2V0+1` and `n0>=1`.
If `n0=1`, then `k=2`, `eta=zeta=1`, and `c=2Y+1` lies strictly
between `psi_A(1)=1` and `psi_A(2)=2A`, impossible. Therefore

    k>=8V0+4, c>kY>=k>8q^7, c>X, kappa>0.             (5)

Also `p!=1`, since `c>=3`. The following additional fact is needed only
for the `bV` transport weight. Suppose `p=3`, and let `c3=4A^2-1`.
If `n0>=3`, then `k>32V0^2`. Since `A<4XY` and `Y^3>2`,

    c3<64X^2Y^2<32X^2Y^5=32V0^2*Y<kY<c,

contradicting `c=c3`. Thus `n0=2`, `k=8V0+4`. Put
`u=X+2-2Y`. The exact expansion is

    eta=4Y^2*(X*u+1)+8Y*(X+1)+3-4Y.

If `u<=-1`, then `eta<0` using `Y(X-1)>2(X+1)`;
if `u>=2`, then
`eta-k>=4Y^2+8Y(X+1)-4Y-1>0`. Both contradict `0<eta<k`.
Thus `u` is zero or one. Equivalently, `2Y-X` is one or two.
But `q` divides both `X` and `Y`, and `q>=32`, a contradiction. Hence

    p>=5 and c>c3=4Delta+3.                          (6)

This elementary congruence avoids the more complicated early carrier
divisibility used by the parent's unrestricted-Y unshifted-bV theorem.
It uses only the already literal `q|Y`, never a decoded native rank.

## 4. Both transport signs and late orientation

For `L=V^2`, (4) immediately gives `g*y<V^2/2=L/2`.

For `L=bV`, signs in (4) give `L=|b||V|>0`. Put `S=Delta*I`, so
`Q=S^2`. Pell classification of (2) gives
`|V|=chi_S(j)/S`, with positive odd `j`: an even-index trace is
`+/-1 mod S` and cannot be divisible by `S`. Index one gives `|V|=1`,
already excluded. Index three gives `|V|=4Q-3`. The two possible signs
would give respectively

    Fsq*(b-4Delta)=c-c3,
    Fsq*(b+4Delta)=c+c3.

By (6), both right sides lie strictly between zero and `2c<Fsq`.
Neither can be a multiple of `Fsq`. Therefore `j>=5`, and

    |V|>=16Q^2-20Q+5>8Q^2.

Because `Q=Delta(Fsq-1)>Fsq`, (4) now gives

    |b|>(8Q^2-c)/Fsq>8Fsq-1/2>4Fsq>4g,
    g*y<(3/8)|b||V|<L/2.                            (7)

For both weights the exact identity `e=b-cT+k-1<b`, using (5), gives
`rho<b/D<=|b|/D`. If `B<=-1`, then `Wt<=-L-1/h<-L`, and (1) yields

    n=epsilon*g*y-kappa+Wt+rho<L/2-L+|b|/D<0.

For `L=V^2`, use `|b|<|V|`; for `L=bV`, use `D>2`, `|V|>1`.
This contradicts the positive input `n`. Thus `B>=0`, and its literal
definition gives `C>0`. Only now invoke the inherited mask inequality
`3q<R<q^4-2`. By (5), `c>2R`, and hence `b=cT-R>0`, `V>0`.
No assertion `b>c` is needed; it can fail when `T=1`.

The normalized strong-rank and signed auxiliary-index theorems have
exactly their retained hypotheses: (3), `c>2R`, `c>2p`,
`V=-c mod f`, and `V=-R mod c`. They recover `p=R` and odd `R`;
the fixed mask parity then gives even `q` and odd `J`.

The shifted companions are justified by the same arguments, substituting
the positive integer `T+alpha` for `T`. Their completeness uses the
parent's canonical `Tstar>alpha`. Their source formulas are consequently
included as a conservative intermediate comparison, not as separate ideas.

## 5. Authenticate the first index from the divisor q^4

This is the new carrier argument. Since `z` is integral, (1) cleared
through `hH` gives `D | hH e`. But

    q^4 | D=XY=w*q^4*s,
    gcd(q,h)=1, H=4Y(X+1)-1=-1 mod q.

It follows that **`q^4 | e`**, without assuming `gcd(D,hH)=1`.
The first-Pell recurrence at `P0=2V0+1` gives

    psi_P0(n0)=n0 mod 2V0,
    k=2n0 mod 4V0.

As `q^4|V0=XY^2`, we obtain `q^4 | 2n0-R-1`.
Also `P0>A`. If `n0>=R`, monotonicity of the Pell ordinate in its base
and index would imply `k/2=psi_P0(n0)>=psi_A(R)=c`, contrary to
`c>k`. Hence `1<=n0<R`, and

    |2n0-R-1|<R<q^4.

Thus `2n0=R+1`. Return now to the full congruence: it gives
`4V0 | e`. Since `D=XY` divides `V0=XY^2`, the complete desired
denominator is recovered:

    D | e, and rho=e/D is an integer.                  (8)

The exact index is established before dividing by the full product `D`.
Factors of `D` that may share primes with `hH` cause no difficulty.

## 6. Native endpoint and completeness

After (8), integral carrier recovery gives `H|h*Kpos`. The parent's
uniform ratio lemma applies at scale one to `A=Y(X+1)+1` and
`P0=2XY^2+1`. With `R=2r+1`, `r>=48`, it yields the same strict
whole-product height bound. The accepted universal projection gives

    H | h*(X-2^R)*(2^R*X+1).

The absolute value of this entire product is less than `H`; thus it
vanishes and `X=2^R`. This step does not cancel a nonunit factor through
a composite modulus. Consequently `kappa` is integral. Equation (1)
then shows `Wt` integral. Since `W=1 mod h`, `h|B` and `t>=0` is
integral. The condition `q^3|Y` was literal from the start. The unchanged
fixed-minus parity, half-binomial rounding, and fresh unscaled source
reconstruction at `Y(X+1)+2` now apply. The entire retained coefficient
tuple calibration decodes a finite syntactic ZFC refutation.

Conversely a refutation supplies the parent's canonical outer data,
including `q^3|Y`, `X=2^R`, `R=3 mod 4`, `R>3q`, and integral `t>=0`.
Form the scale-one first and main Pell witnesses; the uniform ratio
theorem gives `eta,zeta>0`. Choose one fresh seed Pell period divisible
by `c^2*tau` and double it as in the parent. This supplies `i>0` and the
strong pair (3). Its canonical auxiliary construction supplies the
positive integer

    Tstar=(Vstar+c+R*f^2)/(c*f^2),
    Vstar=chi_(Delta*I)(R)/(Delta*I), y=psi_(Delta*I)(R).

Set the unshifted input `T=Tstar`. The exact first-index congruence
gives `e` a positive multiple of `4V0`, so `rho=e/(XY)>0` is integral.
The seed growth estimate gives `g>kappa`. Therefore

    n=g*y+(1+hL)*t+rho-kappa>0

is an integer, its carrier is `z=g*y`, and the displayed polynomial
vanishes. This reconstructs all ten positive inputs. The reverse
direction decoded a refutation from every positive zero. Composing the
two directions with the retained syntactic consistency calibration gives

    ZFC proves: (there is no positive zero of N) iff Con(ZFC).

Neither side of that equivalence is asserted separately.

## 7. Exact degree and arithmetic count

Relative to the incoming scale-one q-cube circuits (78/630,79/468), replace
the four rows `X+1,Y(X+1),Y^2,XY^2` by the three rows
`D=XY, A-1=D+Y, V0=D*Y`, and replace the carrier's `Y^2` by `D`.
This saves one multiplication and reduces the denominator's degree from
eight to six. The proven unshifted-T change saves one addition.
All rows, ports, and inputs remain live.

The degrees of `Q,V,G,M,B` are `124,118,78,13,2`. For `L=V^2`,
`deg Z=251`, so `QZ^2` has degree `626`, strictly exceeding the other
final terms. For `L=bV`, `deg Z=139`, so the unique dominant final
term is `-Q*M^2*G*V^2`, of degree `464`.

With `q0=beta*J`, `k0=eta+zeta`, `C0=q0-F-alpha`, their entire
highest homogeneous components are

    [N76]_626 = 2^14*q0^378*w^48*s^110*i^20*k0^64*T^4*C0^2,
    [N77]_464 = -2^10*q0^284*w^36*s^82*i^14*k0^46*T^2.

These are nonzero at the fixed positive `beta`. For the shifted companions
replace `T` by `T+alpha` in these expressions. The verifier collects the
whole highest components symbolically, treating coefficient ports as
degree-zero symbolic indeterminates, and compares them exactly to these
factored expressions. This is a global degree check rather than a degree
estimate from a few numerical evaluations.

## 8. Verification and provenance

`build.py` reads only the two frozen parent JSON circuits and emits four
core circuits plus the two separately proved partial-saturation companions.
`verify.py` checks the literal transformation, full
topology and liveness, whole coefficient bytes, exact leading forms,
the independent displayed formulas, and mutations. It runs in normal and
optimized Python. Those finite checks verify literal algebra and artifacts;
the unbounded number-theoretic proof is Sections 2--6 plus the named
inherited universal Pell and native calibration lemmas.

The baseline is ProveIt main `e0c98c629bf10d30b695884f6b1d2ab361bdf513`,
including `docs/incoming/ConZFC_Certificate_Reductions_2026-10-25.zip`.
The inherited scale-one proof and source-independent unshifted-T arguments
are copied in `upstream/`. No claim of a global simplest equation, fewer
unknowns than existing nine-positive equations, or historical priority for
Pell doubling, product-square extraction, or unshifted-T transport is made.
The new verified point is their composition with the `XY` denominator and
its shared three-operation arithmetic front.
