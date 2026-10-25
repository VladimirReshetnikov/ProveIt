# Linearizing a strong Pell multiplier in eleven integer unknowns

This is a new ordinary mathematical transformation of the mixed eleven-integer
source in `source/parent_mixed_proof.md`. The whole six-coefficient source34
tuple is retained. The two resulting ordinary polynomials have eleven
unrestricted integer unknowns, with exact degree/operation pairs **440/126**
and **412/127**. A binary addition, subtraction, or multiplication, including
a square or fixed scalar multiplication, costs one operation; reuse is free.
These are new degree/cost tradeoffs, not a global simplicity optimum.

The new step replaces a squared free multiplier by a linear one and recovers
its square nature from a coprime product. Variable prime-adic weights preserve
radical separation even though that new multiplier can have arbitrary
3-adic valuation. The proof includes all signed and zero cases before any
Pell classification is invoked.

## 1. Completely specified polynomial

The independent variables are

    j,C,z,h,r,v,w,T,c,n,s in Z.

The fixed positive coefficients are exactly `beta,K0,MC,MF,cone_A,cone_B`
in `coefficients/BINDING.json` and the six compressed integer payloads.
Here `beta=2^1064921-1`, `cone_A=2^1113`, `cone_B=2^666104`; `MF` is
already shifted. Their finite reconstruction is retained in `coefficients/recipe`.
The port names are fixed numerals, not quantified variables. Define

    J=6j+1, q=beta J+1, W=12w+4,
    X=qW, Y=qv, E=XY, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2 eta^2,
    D=3Budget-4, ell=XY^2, L=ell k,
    Dt=1+L(L+k), Dg=1+D Dt s^2, P=Dt Dg,
    U=rc^2, I2=rc^4,
    Df=1+Delta I2, Q=Delta^2 I2, delta=Q-1,
    V=Df(c-R+4UT)-c, Cy=QV^2-1, Da=delta Cy,
    K=X(3c-2X)+2,
    M=2q^2, Dc=MH,
    zc=Dc T+MK+H(v-q^2),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3),
    S=srM^5H,
    A=9S^2 r Df, B=S^2 Da, G=81S^2 r^2 P.

For the direct polynomial let `Z=Sn-Ac`; for the centered polynomial let
`Z=S(n+QV)-Ac`. In both cases the final polynomial is

    N = [(Z^2+A-B-G)^2-4(AZ^2+BG)]^2-64AZ^2BG.       (1)

Every abbreviation is an integer polynomial. The literal graphs
`linear_multiplier11_direct440.json` and
`linear_multiplier11_centered412.json` contain only the eleven variables,
the six fixed coefficients, integer literals, and binary arithmetic.
There is no division, radical, variable exponent, or implicit witness.

The implementation uses `D81=243Budget-324`, `Dg81=81+D81 Dt s^2`
and `P81=Dt Dg81=81P`. This incorporates the fixed scale 81 into the guard
and reuses `S^2 r` between A and G. The paired norm schedule in (1) is
credited to the incoming Round15 construction. The displayed identity

    N = product_(epsilon in {-1,1}^3)
          [Z-epsilon1 sqrt(A)-epsilon2 sqrt(B)-epsilon3 sqrt(G)]

is a polynomial identity, valid even for dependent or nonpositive radicands.

## 2. Unconditional arithmetic and the nonzero bootstrap

The authentic source restrictions imply q is even, q=2 modulo3,
`|q|>=beta-1>=16`, and `|X|>=4|q|`. If v=0 then a=0 and Delta=3.
Otherwise `|a|=|qv(X+1)|>3`, so in either case `Delta>1`.
H is odd and nonzero, `H=3 modulo q`, and therefore `gcd(H,M)=1`.
Also `a=H=Delta=0 modulo3`, because X=2 modulo3.
Finally `Dt=1+ell(ell+1)k^2>=1` on every integer assignment.

The rational polynomial `pi(t)=(t^2+3)(t^3-19)` has no rational root.
Since Dc is nonzero, `Ac=Dc^5 pi(zc/Dc)` is never zero. If S=0 then
A=B=G=0 and (1) reduces to Ac^8, which is nonzero. Thus every zero
of (1) has s and r nonzero.

The auxiliary radicand Da is strictly positive for every such zero,
before any sign of r or c is assumed. If c=0 then Q=0 and Da=1.
If c!=0 and r<0, then Q<0 and both Q-1 and QV^2-1 are negative.
If c!=0 and r>0, then Q>1 and

    Df=1+Delta r c^4>|c|+1.

Writing V=Df*b0-c, either b0=0 and |V|=|c|>=1, or
`|V|>=Df-|c|>1`. Thus QV^2-1>0 in this case too.

The product rDf is nonzero. It is positive whenever c!=0: for r>0
both factors are positive, while for r<0 both are negative. The only
possible negative case is c=0,r<0, when rDf=r.

At a zero a conjugate factor vanishes. Divide it by the nonzero S;
up to independent signs its radical terms are

    3 sqrt(rDf),       sqrt(Da),       9r sqrt(P).       (2)

Since Da>0, a single negative radicand among rDf and P is impossible.
If both were negative, necessarily c=0,r<0; cancellation of their
imaginary parts would require `9(-r)=81r^2(-P)`, or `1=9rP`,
impossible for integers. Consequently rDf>0 and P>0. The latter is
strict rather than weak because `Dg=1 modulo4`: q and both cone
coefficients are even, so Budget and D are multiples of4.

If Budget<=0, the nonzero integer s and Dt>=1 give
`Dg=1+(3Budget-4)Dt s^2<=-3`. This contradicts P>0. Hence
Budget>=4. The standard centered disk argument now gives k!=0,
the common strict sign of q,F,C,q-F-C, and `|c/k-Y|<1/2`.
The c!=0 conclusion is deliberately deferred until Y!=0 has been restored.

## 3. Variable weights separate the three squareclasses

Write `a3=v_3(|r|)`. Since Df=1 modulo3, the positive integer rDf
has 3-adic valuation a3. Also Da=1 modulo3, while P may have any
nonnegative 3-adic valuation `b3=v_3(P)`.

Decompose each positive integer radicand in (2) as a square times a
positive squarefree integer. Distinct squarefree radicals are linearly
independent over Q. Consider any squareclass that appears in the sum.
If its squarefree part has 3-adic valuation epsilon in {0,1}, the
corresponding coefficient valuations are, whenever present,

    auxiliary: 0                    (only epsilon=0),
    strong:    1+(a3-epsilon)/2,
    guard:     2+a3+(b3-epsilon)/2.

The auxiliary coefficient is strictly smallest if present. If strong
and guard occur in the same class, the guard valuation exceeds the strong
valuation by `1+(a3+b3)/2>0`. Thus every nontrivial squareclass has a
unique coefficient of least 3-adic valuation and cannot cancel.
The rationality of the signed sum (2) forces each radicand to be an
integer square.

In particular rDf is a positive square and `gcd(r,Df)=1`. Consequently
either r and Df are positive squares, or they are both negatives of
positive squares. The second possibility is excluded by Df=1 modulo3,
since `-f^2=1 modulo3` has no solution. Therefore

    r=u^2>0,       Df=f^2>0                            (3)

for integers u,f with u>0. This is the essential linear-multiplier
recovery: r was a completely unrestricted integer input.

Since `gcd(Dt,Dg)=1`, positivity and the product-square condition also give
`Dt=tau^2` and `Dg=g^2`. Let `ytilde^2=Da`. The normalized factor is
now an equality of integers and a rational carrier, so `S|Ac`.

## 4. The cubic scale, strong pair, and signed source are restored

Because M^5 divides S, it divides Ac. The homogeneous quintic is monic.
If `p^e||M` and `v_p(zc)=b<e`, its zc^5 term has valuation 5b and
every other term has strictly larger valuation, since p^e divides Dc.
This contradicts p^(5e)|Ac. Thus M|zc. Reduction modulo M and
`gcd(M,H)=1` give

    v=q^2(2v_old+1),       Y=(2v_old+1)q^3.             (4)

In particular Y!=0. If c=0, the already positive budget would instead be

    Budget=k^2[q^2(1-4Y^2)-Derr]<=0,

a contradiction. Thus c!=0. Define the proof-only integer `I=c^2 u`.
Equation (3) yields

    f^2-Delta I^2=1,       Q=(Delta I)^2>1,
    V=f^2(c-R+4I T_old)-c,       T_old=uT.              (5)

In particular c^2|I, V=-c modulo f, and V=-R modulo c. The quotient
`y=ytilde/(Q-1)` is rational and satisfies

    QV^2-(Q-1)y^2=1.

The retained adjacent-coefficient Pell descent makes y integral; its
required Q>1 hypothesis has now been established. For reference, with
y=a/b reduced one has b^2|Q-1. The transformation

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

keeps V' integral and the reduced denominator b, while after reflecting
signs it strictly reduces |V| unless |V|=1. At that endpoint |y|=1,
so b=1.

All the parent's pre-projection hypotheses now hold, with exactly the
same outer tuple and the strong pair in (5). They use c^2|I and the two
residues; they do not require T_old to be arbitrary, or I/c^2 to be odd.
The retained signed-folding and rank proof therefore gives

    c=sign(c) psi_(a+2)(R),       R=2t+1, t>=24,
    |Y|>(|X|-3)^t/2-1,       |H|>|X|(|X|-3)^t.

Also H|Ac and zc=MK modulo H give H|K^5. Since
`K=HXc-2[X(X+2ac)-1]` and H is odd, the parent fifth-power projection
applies unchanged. More explicitly, with x=|X|, sigma=sign(c),

    Pi=(sigma X-2^R)(2^R sigma X+1),
    H|Pi^5,
    |Pi|^5<2^(20t+20)x^10<x^(t+1)/2^t<|H|.

The authentic beta gives x>=2^64, and the middle inequality follows from
`64(t-9)>21t+20` for t>=24. Hence Pi=0 and sigma X=2^R.
The parent's final orientation and centered half-binomial recovery then
give X,c,k,Y>0 and `0<eta/k<1/4`. Its fresh odd-witness restoration
produces the exact old native source zero.

Thus every zero of the new polynomial gives a finite syntactic ZFC
refutation after composing the retained ordinary native/compiler calibration.
No implication about the truth of consistency itself is asserted.

## 5. Complete converse with the strong pair fixed before interpolation

Start with a finite refutation and the parent's canonical outer witness.
Use (4) to choose the new v. It gives `Dt=tau^2`, Budget>=64,
`Dt=1 modulo3`, and `D=2 modulo3`. Hence D Dt is positive and nonsquare.
Choose a positive guard Pell solution `g^2-D Dt s^2=1`.

Now choose one positive strong pair I,f, by the retained finite matrix
period argument, such that `4s c^2|I`. Keep it fixed. Define

    u=I/c^2,       r=u^2,       m=sr=s u^2.

The supported-modulus interpolation theorem in `source/POWERED_PROOF.md`,
Section5, says that this same pair I,f admits every T_old residue modulo
any positive modulus whose prime divisors divide I. This theorem is
stronger than interpolation merely modulo I. Its proof uses the exact
p-adic isometry of the index progression and is retained in full.

The canonical main projection gives H|K. Put

    kappa=K/H+(v-q^2)/M in Z.

The intersective quintic pi has a root in every residue ring. Choose
`a0 mod m` with `pi(a0+kappa)=0 mod m`. Every prime dividing `um=s u^3`
divides I. Apply supported-modulus interpolation with that modulus to
request

    T_old=u a0 modulo um.

It gives an auxiliary integer y while leaving I,f fixed. The congruence
makes `T=T_old/u` integral and `T=a0 modulo m`. Thus

    Ac=Dc^5 pi(T+kappa),
    Ac/S=H^4 pi(T+kappa)/(sr) in Z.

Notice that no strong pair was reselected after this residue request.
The extra multiplication by u in the interpolation modulus is what
licenses division of the auxiliary coordinate by u.

At these constructed values sqrt(rDf)=u f, sqrt(Da)=delta y,
and sqrt(P)=tau g. Choose

    n=Ac/S+3u f+delta y+9r tau g                       (direct),
    n=Ac/S+3u f+delta y+9r tau g-QV                    (centered).

Then one conjugate factor of (1) vanishes. All eleven inputs are integers.
This proves the reverse implication, hence the two integer-zero existence
equivalences. The direct and centered polynomials are additionally related
by the polynomial coordinate bijection `n_direct=n_centered+QV`.

The intersectivity of pi and the signed/native calibration are inherited
from the named source. Its elementary local-root proof and the complete
signed rank/projection/interval proofs are included in the source excerpts.
The new work is the linear multiplier, its signed bootstrap, the variable
prime-adic weights, and the rescaled use of supported-modulus interpolation.

## 6. Exact total degrees after authentic coefficient specialization

Every independent variable has degree1 and every fixed numeral degree0.
The key exact degrees are

    I2:5, U:3, Df:13, Q:21, V:18, Da:78,
    Dt:22, Budget:16, Dg:40, P:62,
    S:16, Ac:35, A:46, B:110, G:96.

For the direct equation deg Z=35 and B is the unique dominant radicand.
The highest form is B_top^4, giving degree440.

For the centered equation, put `C0=SQV` and `Z0=Sn-Ac`.
The exact identity

    B-C0^2=-S^2[Q(V^2+1)-1]

shows that omega=Z^2-B has degree at most90. In the identical symmetric
norm form

    [(omega-A-G)^2-4(AG+AB+BG)]^2-64ABGZ^2,

the inner bracket has unique highest term -4BG, of degree206; the other
bracket terms have degree at most192,142,156. The final correction has
degree362. Thus the centered highest form is 16 B_top^2 G_top^2 and
its exact degree is412.

For complete leading forms write

    q0=6 beta j, X0=12q0 w, Y0=q0 v, a0=X0Y0,
    R0=-q0^3(12wC-q0z), k0=R0+h a0.

Then

    B_top=2^14 s^2 r^6 q0^20 a0^14 c^16 R0^2,
    G_top=-2^16 3^5 s^4 r^4 q0^22 X0^6 Y0^12 k0^6.

The entire centered degree412 part is

    2^64 3^10 s^12 r^20 c^32 q0^84 X0^40 Y0^52 R0^4 k0^12.

The following actual coefficients are nonzero at the complete fixed tuple:

    [j^216 w^52 v^64 h^12 z^4 s^12 r^20 c^32] N_centered
        =2^384 3^278 beta^216,
    [j^224 w^56 v^56 z^8 s^8 r^24 c^64] N_direct
        =2^392 3^280 beta^224.

Their exponent sums are412 and440. The argument concerns the whole
polynomial, not values at solutions or a univariate numerical sample.

## 7. What is established and what remains inherited

The ordinary proof composes with the same whole source34 calibration:

    ZFC proves (no integer zero of N) iff Con(ZFC).

This is not a proof of either side, a new globally minimal equation, or
a complete Lean/Rocq or encoded object-language ZFC certificate. The
logical calibration is an identified inherited ordinary theorem.
Without adopting that calibration, the unconditional new result is the
proved equivalence between the new arithmetic zero condition and its
predecessor source zero condition.

`verify.py` imports no producer or DAG builder. It authenticates all six
complete numeral payloads; checks every named register by local exact
integer-polynomial identities; expands all eight conjugate factors and
checks every one of their35 coefficients; proves the centering and
restoration identities; recomputes the whole leading forms and attained
coefficients; recounts live operations and all eleven variables; and
rejects seven changed circuit nodes per variant. Its bounded arithmetic
tests are regression controls only. They are not used as proofs of the
unbounded statements above.

Further research questions are whether the same linear-multiplier device
can absorb other repeated Pell squares without adding root weights, whether
the carrier can use a lower-degree intersective family under restricted
prime support, and whether the signed bootstrap and supported-modulus
interpolation can be formalized once for reuse. None is asserted solved here.
