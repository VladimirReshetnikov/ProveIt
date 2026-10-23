# Twenty-six unrestricted integer unknowns

This construction combines the twelve-coordinate weighted-root norm with
the signed half-binomial-scale argument. It uses more arithmetic and higher
degree than the 27-integer circuits, but one fewer unrestricted integer.
It does not assume that the H-divisible strong multiplier can be odd.

## 1. Actual unknowns and retained expressions

The seven guarded ports are

    J,F,alpha,z,i,eta,zeta.

Replace each by its own disjoint copy of

    Pos(u,v,r)=1+u^2+v^2+r(r+1).

This expression is positive for all integer inputs and represents every
positive integer by the three-square theorem applied to `4n-3`. The other
five unrestricted integer unknowns are

    h,T,t,s_integer,w_integer,

and the two remaining source ports mean

    s=2*s_integer+1, w=w_integer^2.

There are therefore exactly `7*3+5=26` unrestricted integer unknowns. In
particular i is a guarded positive integer, not an odd affine expression.

Use a single coherent authentic coefficient tuple and define

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H, P=X+ac, S=1+Delta c^2,
    L=E kY, A=1+L(L+k),
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MFsrc)J,
    Nk=k-hE-R, Nt=(kappa+w)C+q-F-z(q-1),
    G=H i c^2, D=1+Delta G^2, Q=Delta(D-1)=(Delta G)^2,
    d=Q-1, v=cT, b=c+RD,
    e=Q(Dv^2+b^2)-1, Baux=2Qvb.

All these are polynomial abbreviations. No additional unknown is introduced.
The source port MFsrc is the shifted high mask.

## 2. Bounds that hold before any root is reconstructed

At a zero of the final product, its unit-guard argument below gives
`Nk,Nt` integer units. The ordinary system states them equal to one.
Weak transport, using only the guarded ports and `w>=0`, yields `C>=0`:
if C were at most -1, then

    Nt=(kappa+w)C+1-F-(z-1)(q-1)<=-(kappa+w)<=-2.

Thus `q-F=C+alpha>0`. Authentic mask bounds give

    q>=16, q(q^2-1)<R<q^4-2.                      (1)

These bounds do not assume `X>0`. Initially X may be zero.

Since s is odd, `|Y|>=q^3`. Also `X>=0`, so `|a|=(X+1)|Y|>=q^3`.
The numbers a and c have the same sign. If Y is negative then
`|c|=k|Y|-eta>k(|Y|-1)`; if Y is positive then `c>kY`. In both cases
`|c|>1` and `|H|>1`. Hence

    Delta >= (q^3-1)(q^3-3)>q^4>R,
    S>1, G!=0, D>1, Q>1, d>0.                    (2)

The first radicand is positive even at the zero-scale boundary:
`L=X kY^2>=0`, so `A=1+L(L+k)>=1`. In particular A=1 is explicitly
allowed before X=0 is excluded later.

Because `G^2=H^2 i^2 c^4>=c^4` and `|c|>1`,

    D=1+Delta G^2>Delta+|c|.

Consequently

    b=c+RD>D-|c|>1,
    Q-b=(Delta-R)D-Delta-c>D-Delta-|c|>0.

Thus the useful strict interval is

    1<b<Q.                                       (3)

No sign assumption on h, T, t, Y, or H has entered these estimates.

## 3. Positive separating weights for the signed domain

The twelve-positive-variable weights do not work unchanged when T or H
is negative. Replace them by the following explicit positive polynomials:

    Ubound=(T^2+1)(a^2+5)H^2 i c^4,
    M=1+2(Ubound+b),
    N=1+H^2 M(A+1).                               (4)

In particular `N=1 (mod H)` and `gcd(N,H)=1`.

Consider the algebraic root equations

    (P+H gamma)^2=S, tau^2=A,
    (d y^2-e)^2=Baux^2 D.                         (5)

All roots in (5) are considered, including complex y branches. Every y
branch can be paired with some `f=+sqrt(D)` or `-sqrt(D)` such that

    d y^2=Q(vf-b)^2-1.

Since Q>=2 and `|v|sqrt(D)+b>1`,

    |y|<2(|v|sqrt(D)+b).

Moreover `sqrt(D)<|a+2| |G|`, because G squared exceeds one and
`Delta=(a+2)^2-1`. The elementary integer inequalities

    |T|<=T^2+1, |a+2|<=a^2+5, |H|<=H^2, |c|^3<=c^4

give `|v|sqrt(D)<=Ubound`. Therefore

    |y|<M.                                       (6)

Since A>=1 and S>1, equation (4) yields

    N sqrt(S)/|H| > M(A+1)
                 >= M sqrt(A)+M
                 > M sqrt(A)+|y|.               (7)

These strict bounds imply injectivity of

    (gamma,tau,y) -> y+M tau+N gamma               (8)

on the distinct triples satisfying (5). If gamma changes, its difference
has magnitude `2sqrt(S)/|H|`, and (7) dominates all possible tau and y
differences. If gamma is fixed but tau changes, its contribution has
magnitude `2M sqrt(A)>=2M`, which exceeds the difference of two y branches
by (6). If both are fixed, the displayed value directly fixes y.

At this stage no assertion is made that the corresponding f is unique:
when T=0, Baux=0 and f is absent from the auxiliary root equation. Handling
this degeneracy explicitly is necessary.

## 4. Literal polynomial

Use exactly the same two quadratic norms as the twelve-variable reduction,
with the new weights (4). For clarity, put

    W=Ht+NP, m=HM,
    a0=d(W^2+m^2 A+N^2 S)-H^2 e,
    a1=-2dWm, a2=-2dWN, a3=2dmN,
    f0=a0^2+A a1^2+S a2^2+AS a3^2-H^4 Baux^2 D,
    f1=2(a0 a1+S a2 a3),
    f2=2(a0 a2+A a1 a3),
    f3=2(a0 a3+a1 a2),
    U=f0^2+A f1^2-S(f2^2+A f3^2),
    Vnorm=2(f0 f1-S f2 f3),
    Norm26=U^2-A Vnorm^2.

The system is

    Nk=1, Nt=1, Norm26=0.                         (9)

The single product polynomial is

    P26=Nk Nt(1+Norm26)-1.                        (10)

The emitted straight-line circuits expand all abbreviations, including the
seven positive surjections and two elementary substitutions. They use only
integer coefficients and binary addition, subtraction and multiplication.

As a product over algebraic roots, Norm26 equals

    d^8 H^16 product(t-y-M tau-N gamma),

with sixteen factors and multiplicity. The product identity remains true
if A or S is already a square, if the quadratic extensions coincide, or
if Baux=0 causes repeated auxiliary roots.

## 5. Rationality and integrality, including T=0

At integer values of the 26 unknowns, `Norm26=0` gives a triple (5) with
the indicated integer t. Every automorphism of a finite normal closure
over the rationals preserves its t and the root equations. Injectivity
(8) fixes gamma, tau, and y. Hence these three numbers are rational.

The rational square roots `tau^2=A` and `u^2=S`, where `u=P+H gamma`, are
integers. Thus the reduced denominator of gamma divides H.

To control y without assuming T nonzero, use its quartic directly:

    d^2 y^4-2de y^2+e^2-Baux^2 D=0.

If `y=r/s` is in lowest terms and a prime divides s, multiplying by s^4
and reducing modulo that prime shows that the prime divides d. Since
`Q=0 (mod H)` and `d=Q-1`, `gcd(d,H)=1`. Thus the denominator of y is
coprime to H. But

    y+N gamma=t-M tau

is an integer, so the denominator of y also divides H. It is one.
Then N gamma is integral; `gcd(N,H)=1` makes gamma integral too.
This establishes integer y and gamma even when T=0.

Now suppose T=0. Then v=Baux=0, so (5) implies `d y^2=e=Q b^2-1`.
Equivalently,

    d(y^2-b^2)=b^2-1>0.

By integrality `|y|>=b+1`. By (3), `d=Q-1>=b`. Therefore the left side
is at least `d(2b+1)>=b(2b+1)>b^2-1`, a contradiction. This excludes
the only coefficient-degeneracy case without appealing to an asymptotic
or unproved Pell assertion.

Thus T is nonzero and `Baux=2Q cT b` is nonzero. Define

    f=(e-d y^2)/Baux.

Equation (5) gives `f^2=D`, so f is an integer. The four reconstructed
roots satisfy precisely

    (P+H gamma)^2=S, tau^2=A,
    f^2-Delta(H i)^2 c^4=1,
    Q[c(Tf-1)-Rf^2]^2-(Q-1)y^2=1.                 (11)

No positivity of the reconstructed gamma, f, tau, or y has been assumed.

## 6. Exclude zero w and negative s; recover the compiler

If X=0, the reconstructed main root is `P+H gamma=ac+H gamma`.
Reducing its norm equation modulo H gives `0=1 (mod H)`, impossible
because `|H|>1`. Thus w>0 and X>=q.

The proof `ODD_SCALE_27_PROOF.md`, Sections 1-4, now excludes negative s.
That soundness argument uses only that the normalized strong multiplier
is nonzero. Its odd parametrization was a way to ensure nonzeroness and
preserve canonical completeness; oddness plays no role in its negative-s
exclusion. In (11) the multiplier H i is nonzero by (2), which suffices.

Explicitly, if `Z=-Y>0`, set `B=(X+1)Z-2`, `c0=-c`, and
`P0=2XZ^2+1`. First/main Pell classification and the signed auxiliary
congruences recover p=R. No wrap and the strict ratio recover
`R=2r+1`, and

    Z> (1/2)[(2B-1)^2/(2P0)]^r >X^r/2>2^R.

The two possible signs of the main root then give either
`X+2^R=0 (mod H)` or `X2^R=1 (mod H)`. Both contradict the strict
intervals `0<X+2^R<|H|` and `1<X2^R<XZ<|H|`. Hence s>0.

All nine required compiler coordinates are now positive, with normalized
strong multiplier `H i>0`. The ordinary signed-parent theorem applies
using `i_ordinary=Delta H i`, allowing the reconstructed roots and h,T
to be signed. Its rank and power extraction prove that K215 halts on
blank input. The preceding negative-s argument already allowed the two
common unit signs of Nk,Nt; the signed-parent proof forces both signs
positive before extracting the native tableau.

For (10), the three displayed factors are units. Vnorm is even, so
Norm26 is a square modulo four. Consequently `1+Norm26` cannot be -1
and must be 1. Thus `Norm26=0`, `Nk Nt=1`, and the weak-bootstrap proof
above applies. This justifies the proof order used in Section 2.

## 7. Completeness

Start from a canonical accepting blank tableau. The existing five-power
padding can make the exponent of q odd, and the actual rank R is odd;
hence the canonical scale `w=2^R/q` is a square.

The exact native population identity proved in `ODD_SCALE_27_PROOF.md`,
Section 5, gives `popcount(R)=3 log2(q)+2`. The half-binomial identity
then gives `v2(Y)=3 log2(q)`, so s is positive and odd.

Choose the strong Pell index m as a common multiple of R and a period of
the invertible Pell matrix modulo `Hc^2`. This supplies a positive
integer `i=psi_(a+2)(m)/(Hc^2)`; no claim that i is odd is needed.
The construction detailed in `INDEPENDENT_TWELVE_AUDIT.md` supplies the
positive f, y, T and the corresponding positive main/first roots. Set

    t=y+M tau+N gamma.

The weights are positive, so this integer is even positive, though the
26-variable construction does not require that restriction. Every guarded
positive port has a Pos representation; use `(s-1)/2` and an integer
square root of w for the two remaining substitutions. One norm factor
vanishes, giving both (9) and (10).

This proves existence equivalence. Composition with the authentic compiler
and the K215 refutation endpoint gives the ZFC-provable equivalence between
unsolvability of the 26-integer construction and Con(ZFC).

## 8. Exact degrees, operation counts, and evidence

The substitutions assign degree two to `J,F,alpha,z,i,eta,zeta,w`, degree
one to `s,h,T,t`. The leading degrees are

    c:9, E,a,H:11, Delta:22, R:8, A,S:40,
    G:31, D:84, Q,d:106, b:92, M:92, N:154.

The first summand Ubound in (4) has degree 84, so `M_top=2 b_top`.
The two main-root gamma branches have degrees 9 and -2. Indeed

    H^2 gamma^2+2HP gamma+(P^2-S)=0,
    P^2-S=X^2+2Xac-Hc^2-1,

and the three coefficient degrees are 22,31,29. The two N gamma branches
therefore have degrees 163 and 152, whereas `M tau` has degree 112 and
every auxiliary y branch has degree 92. Thus in every factor the N gamma
term is uniquely dominant. Pairing the two gamma branches gives

    (Norm26)_3544
       =d_top^8 N_top^16 [(P^2-S)_top]^8
       =d_top^8 N_top^16 (H_top c_top^2)^8,

which is nonzero for every authentic fixed coefficient tuple. The degree
is `8*106+16*154+8*29=3544`. Nk and Nt have degrees 12 and 4, with
nonzero leading forms, so the product has exact degree 3560. The sum of
three squared residuals has exact degree 7088.

| Construction | Unknowns | Equations | Degree | Gates |
| --- | ---: | ---: | ---: | ---: |
| Comparison system | 26 integers | 3 | 3544 | 195 |
| Residual system | 26 integers | 3 | 3544 | 197 |
| Product polynomial | 26 integers | 1 | 3560 | 199 |
| Sum of squares | 26 integers | 1 | 7088 | 202 |

Comparisons in the first row are free, in the repository convention. The
residual row explicitly subtracts the two constants one. Both include
all 52 substitution gates and the complete live norm evaluator.

Run `python3 build_integer26.py --degree` to regenerate every JSON circuit
and the verification receipt. The standard-library-only checks include
48 signed integer evaluations against an independent direct norm formula,
bounds covering both signs of s and the X=0 boundary, denominator
coprimality, the unit guard, a synthetic auxiliary-root fixture, and exact
modular polynomial degree/leading-coefficient checks. The accompanying
structural proof, not finite sampling, establishes the universal claims.

The result does not have a new Lean/Rocq proof, does not decide whether
solutions exist, and does not establish global minimum variable count.
