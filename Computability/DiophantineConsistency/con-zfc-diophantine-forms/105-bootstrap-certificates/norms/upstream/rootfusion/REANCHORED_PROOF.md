# Moving a nonzero scale inside a joint positivity guard

## Result and scope

The incoming `ConZFC_13_Integer_Norms_2026-10-24.zip` specifies a polynomial
in 13 unrestricted integer variables, degree 1088, using 195 binary arithmetic
operations. Moving its factor v^2 inside the first argument of the joint guard
gives an existence-equivalent equation of **exact degree 1072 with the same 13
variables and 195 operations**. The six fixed coefficients are unchanged.

This is a small secondary improvement, separate from the direct proof-calculus
compiler. It retains the complete ordinary calibration dependencies of its
parent. The new part is the guard reduction and degree computation, not a new
K215-to-ZFC proof or a global variable-count claim. Package 73's earlier
reanchoring of common-sign constraints is a distinct mechanism; the present
comparison is specifically to the displayed incoming CRT1088 polynomial.

## A general guard lemma

Define, for integers x,y,t,

    Pair(x,y,t) = xy-(t^2-x-y+1)^2.

Then `exists t in Z, Pair(x,y,t)>0` if and only if x>0 and y>0. For soundness,
positive Pair first implies xy>0. If x=-a,y=-b with a,b>0, its subtracted
square is at least (a+b+1)^2>ab, a contradiction. Thus both are positive.
Conversely put N=x+y-1. A nearest integer square t^2 satisfies
`(t^2-N)^2<N`: between m^2 and (m+1)^2 a nearest square differs from the
integer N by at most m, with strict squared error <N; the square endpoints
are immediate. Since `N<=xy`, the resulting Pair is positive.

Also `Pos(p1,p2,p3)=1+p1^2+p2^2+p3(p3+1)` represents exactly the positive
integers. Its values are positive because the consecutive product is
nonnegative on Z. For surjectivity apply the three-square theorem to 4n-3,
which is positive and 1 modulo 4, hence is never of the excluded form
4^a(8b+7). In any representation there is one odd and two even coordinates;
rescaling them gives exactly the displayed Pos formula.

Consequently each of the following conditions on fixed integers v,G,T is
equivalent to `v!=0, G>0, T>0`:

    exists t,p1,p2,p3: v^2 Pair(G,T,t)=Pos(p1,p2,p3),
    exists t,p1,p2,p3: Pair(v^2 G,T,t)=Pos(p1,p2,p3).

The private witnesses need not agree. This is an existential equivalence,
not an identity between the two guard polynomials.

## The complete change to the CRT norm

Keep all coordinates and all front-end definitions from the parent's
`report/crt1088.tex`. In particular the independent coordinates are

    j,C,z,h,r,v,w,T,c,n,t,p2,p3 in Z.

Use `J=6j+1`, `q=beta J+1`, `W=12w+4`, `X=qW`, `Y=qv`,
`a=(X+1)Y`, `H=4a+3`, `Delta=a^2+H`, `eta=c-Yk`, `zeta=k-eta`, and

    G = (cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2.

The old guard radicand was

    Ag_old = v^2 Pair(G,eta*zeta,t)-1-p2^2-p3(p3+1).

Replace it by the following polynomial, and change nothing else:

    Ag_new = Pair(v^2 G,eta*zeta,t)-1-p2^2-p3(p3+1)
           = v^2 G eta zeta-(t^2-v^2 G-eta*zeta+1)^2
             -1-p2^2-p3(p3+1).

The full polynomial is still the parent's cleared five-radical norm

    delta^16 F32(Z;
        M^2 Lambda^2 Dmain,
        U^2 Df,
        U^2 Dtau,
        U^2 Ag_new,
        U^2 Cy/delta),

where `M=2q^2`, `Lambda=4H+1`, `U=MH`, and the rest of the definitions are
literally present in `build_reanchored.py` and the emitted `equation.json`.
F32 is the product over all 32 independent radical signs. The inherited
division-free evaluator eliminates the formal roots and denominator; the
emitted graph uses only integer leaves and binary +, -, and multiplication.

## Soundness, with exceptional branches included

The parent's unconditional analysis is unchanged: delta and U never vanish,
and the four non-guard radicands are strictly positive for every integer
assignment, including v=0 and c=0. At a polynomial zero a conjugate factor
vanishes. If Ag_new were negative, its square root would be the sole nonzero
imaginary term of that factor. Hence Ag_new>=0 and

    Pair(v^2 G,eta*zeta,t)
       =Ag_new+1+p2^2+p3(p3+1)>0.

The guard lemma proves v^2G>0 and eta*zeta>0, so v!=0, G>0, and eta*zeta>0.
These are exactly the source conditions previously recovered. In particular
the zero-v branch is excluded by the guard, and the zero-c branch is excluded
by eta*zeta=-Y(Y+1)k^2<=0 when c=0.

Every magnitude-separation estimate also survives. Since the subtracted square
and the positive Pos remainder are nonnegative/positive,

    Ag_new < v^2 G eta*zeta.

Writing K=|k|, the already proved G<q^2 and eta*zeta<=K^2/4 give

    sqrt(Ag_new)<|v| |q| K/2.

This is precisely the bound used in the parent's CRT proof. Thus its strict
superincreasing orders, radical square-class extraction, rational Pell
descent, two coprime congruence recoveries, and restored kernel all apply.
No new sign premise, coprimality premise, or consistency assumption is added.

## Completeness

Start with a canonical source-kernel witness and the parent's CRT value
`v=Y/q!=0`. Both v^2G and eta*zeta are positive. Choose t by the guard lemma
so `Pair(v^2G,eta*zeta,t)>0`, and then choose p1,p2,p3 by Pos surjectivity.
The new guard radicand is p1^2. All four Pell radicands, the native coordinates,
and the fixed coefficients retain their old values. Finally choose the norm
center coordinate exactly as before, but with this newly chosen p1:

    n=Lambda*gamma+f+tau+p1+y-V-(v-q^2)/M.

This is integral by the already established source congruences and makes one
norm factor zero. Hence the modified polynomial has an integer zero exactly
when the parent's calibrated source kernel does. Negating and composing the
inherited ordinary theorem gives the same ZFC consistency biconditional.

## Exact degree and count

The relevant leading degree of eta is 7. Thus eta*zeta has degree 14, and
its square has degree 28. The old outer v^2 raised that to 30. In the new
formula, v^2G has degree 6, so the unique degree-28 guard component is
`-eta_0^4`, where eta_0 is the degree-seven homogeneous part of eta.
The scaled guard radicand e=U^2 Ag_new therefore has degree 40, formerly 42.

The independent exact cut calculation uses variables
`U,s,V,d,A,B,e,delta` with weights `(6,11,19,22,26,34,40,22)` and
`Z=UV+s`. In the biquadratic extension with root weights 11 and 20, the
four weighted component degrees through the three-root norm are:

    J: [62,58,67,53],
    K: [134,120,129,125],
    F: [268,254,263,259].

The unique highest component is scalar, equal to
`16 delta_0^4 U_0^4 V_0^4 e_0^2`. Taking the last two quadratic norms
squares this top part twice, so the final degree is 4*268=1072.

With the parent's explicit leading definitions q0,a0,i0,R0,eta0, the complete
top form is

    2^112 q0^64 a0^128 i0^64 c^128 R0^16 eta0^32.

In particular the coefficient of

    j^480 w^160 v^192 h^32 r^64 c^128 z^16

is `2^976 3^640 beta^480`, strictly positive on the actual fixed tuple.
The exponent sum is 1072. Therefore this is an exact degree, not merely a
syntactic upper bound. `verify_reanchored.py` checks the entire cut degrees,
the unique top component, and this numerical-slice coefficient symbolically.

One old multiplication `v^2*Pair` is replaced by the multiplication `v^2*G`.
No other live gate changes in number. The rebuilt graph has 41 additions,
122 multiplications, and 32 subtractions: 195 operations in all. Every
declared variable remains live. The reduction is 16 degrees, about 1.47%,
with unchanged dimension and arithmetic operation count.

## Reproduction and limitations

Run `python3 build_reanchored.py`, then `python3 verify_reanchored.py`.
The checked literal hash and receipt are in `AUDIT.json`. Besides exact
algebra/degree checks, 45 modular evaluations against an independent formal
conjugate-product implementation cover ordinary and exceptional slices. Those
samples are transcription diagnostics, not the proof of the universal
equivalence. The mathematical proof is the guard argument above composed with
the parent's retained ordinary source/Pell/calibration proof.
