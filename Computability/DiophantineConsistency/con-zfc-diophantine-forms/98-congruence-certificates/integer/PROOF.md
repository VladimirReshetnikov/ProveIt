# CRT and valuation composition: 13 integer unknowns, degree 1072

## Result and dependencies

The complete literal equation is `equations/integer13_crt_valuation_degree1072.json`.
It has 13 unrestricted integer unknowns, exact degree 1072, and 195 live binary
arithmetic operations. The six fixed numerical leaves are the complete source34
tuple and the two determinant scales, copied from the root-fusion archive. The
whole binding and literal bytes are in `coefficients/`; MF is already shifted.

The new reduction combines the coprime carrier of the incoming
`ConZFC_13_Integer_Norms_2026-10-24.zip`, section CRT1088, and the valuation
separation/pentagonal positivity lemmas of
`ConZFC_FixedPrime_Radicals_2026-10-23.zip`. In particular, this is a completed
algebraic reduction relative to their identical normalized source system Cal.
The inherited Cal/native/K215/refutation calibration is unchanged. Its ordinary
mathematical theorem is the named dependency for the concluding ZFC-provable
consistency equivalence, not a new proof-assistant result.

The comparison is 1088/195 for the incoming CRT form and 1392/475 for the
fixed-prime form. We lower degree by 16 at the same operation count as
CRT1088. This is an incremental improvement, not a breakthrough or global
minimum claim.

## Complete equation

The variables, in circuit order, are

    j,C,z,h,r,v,w,T,c,n,t,p2,p3 in Z.

All other symbols below are polynomial abbreviations. Put

    J=6j+1, q=beta*J+1, W=12w+4, X=qW, Y=qv,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    F=(K0+W)C-z(q-1), alpha=q-F-C,
    R=(q(q-F)-C)(q^2-1)+(MC+q*MF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    I=(2r+1)c^2, Df=1+Delta*I^2, Q=Delta^2*I^2, delta=Q-1,
    V=Df(cT-R)-c, Cy=QV^2-1,
    Dtau=1+XY^2(XY^2+1)k^2, Dmain=1+Delta*c^2, b0=X+ac,
    G=(cone_A*F)(cone_B*C)-(q-cone_A*F-cone_B*C)^2,
    Z=eta*zeta, N=GZ-(t^2-G-Z+1)^2,
    S=24N-21-(6p2-1)^2-(6p3-1)^2,
    M=2q^2, U=MH,
    p=U(n+V)+M*b0+H(v-q^2).

Define the universal sign product

    F5(x;d1,...,d5) = product_(epsilon in {+1,-1}^5)
                      (x-sum_i epsilon_i*sqrt(di)).

Sign invariance gives F5 in Z[x,d1,...,d5]. Each di has exponent at most16.
The final ordinary integer polynomial is

    P = delta^16 F5(p;
          81 U^2 Dtau, 9 U^2 Df, M^2 Dmain,
          729 U^2 S, U^2 Cy/delta).

The denominator clears identically. The accompanying DAG gives a division-free
evaluation using the inherited, exact five-root norm identity. No symbol above
is an extra unknown and the proof-only square roots do not occur in the DAG.

## Universal congruences and separation

The fixed exponent 1064921 is odd, so beta=2^1064921-1 is odd and beta=1 mod3.
Consequently q is even, q=2 mod3, and q never vanishes. Also W=1 mod3 and
X=2 mod3. Hence a=(X+1)Y=0 mod3, so H and Delta are multiples of3.
The integer H=4a+3 never vanishes. We have

    Df = Dmain = 1 mod3,
    Dtau = 1 mod3,
    S = 1 mod3,
    Q = 0 mod3, delta = -1 mod3, Cy = -1 mod3.

For Dtau, XY^2 is either0 or2 mod3, so XY^2(XY^2+1)=0 mod3.
For S, each 6pi-1 is -1 mod3. In particular delta!=0 before any guards or
positivity are recovered, and Cy/delta is a nonzero 3-adic unit.
The other four raw radicands are also nonzero units, even when negative.

Let e=v_3(H)>=1. Since v_3(M)=0, the five weighted radicands have valuations

    2e+4, 2e+2, 0, 2e+6, 2e,

which are pairwise distinct even integers.

**Valuation lemma.** Suppose nonzero rational d_i have pairwise distinct even
valuations at one prime. If a signed sum of their square roots is rational,
then each d_i is a rational square. Indeed, group terms by rational square
class. Distinct square classes are linearly independent over Q; within a
nontrivial class, all coefficients are rational and have pairwise distinct
valuations up to a common shift. Their signed sum cannot vanish because its
least valuation occurs uniquely. Thus no nontrivial square class can occur.
This proof also covers negative d_i and complex roots.

At P=0, a sign factor vanishes, so the lemma supplies signed rational roots
tau,f,d,s,y of Dtau,Df,Dmain,S,Cy/delta respectively satisfying

    p = 9U*tau + 3U*f + M*d + 27U*s + U*y.       (1)

The first four roots are integers because rational roots of monic quadratic
integer polynomials are integers. Integrality of y follows below. This does
not use Archimedean size or positivity of any raw radicand.

## Recover guards and the rational auxiliary root

From S=s^2, the identity

    24N-21 = (6p2-1)^2 + (6p3-1)^2 + s^2

implies N>0. The standard joint-positivity lemma then gives G>0 and Z>0:
if G,Z were both negative, |t^2-G-Z+1|>|GZ|^(1/2), a contradiction;
their product is positive because N>0. Conversely G,Z>0 permits such t by
choosing a square nearest to G+Z-1, whose squared error is smaller than GZ.

The inequality Z=eta*zeta>0 excludes c=0 because that would give
Z=-Y(Y+1)k^2<=0 for the integer Y. Therefore c!=0.

Unconditionally, either v=0, when a=0 and Delta=3, or v!=0, when
|q|>=16, |X|>=64, |Y|>=16, and |a|>=63*16, hence Delta>1. Thus Delta>=3
in either case. Since 2r+1 and c are nonzero, Q>=9>1.

**Adjacent-coefficient descent.** If Q>1, V in Z and y in Q satisfy
QV^2-(Q-1)y^2=1, then y is integral. Write y=b/d in lowest terms.
Then d^2 divides Q-1. The descent

    V'=(2Q-1)V-2(Q-1)y,  y'=(2Q-1)y-2QV

preserves the norm and reduced denominator, makes V' integral, and after
sign changes has 0<|V'|<|V| when |V|>1. At |V|=1 the equation gives |y|=1.
This is the inherited elementary rational Pell descent and proves d=1.
Apply it to y^2=Cy/delta. Now every root in (1) is integral.

## Two congruences restore the normalized source exactly

Since Y=qv, H=4(X+1)qv+3=3 modq. Because 3 does not divide q and H is odd,

    gcd(H,M)=gcd(H,2q^2)=1.

Reduce (1) modulo M. It gives H(v-q^2)=0 modM, and therefore

    v=q^2(2v_old+1),   v_old=(v-q^2)/(2q^2) in Z.

In particular v!=0, and Y=(2v_old+1)q^3 is exactly the original scale.
There was no need to multiply N by v^2 to exclude v=0: the square-root
recovery and the CRT congruence now exclude it directly.

Reduce (1) modulo H. It gives M(d-b0)=0 modH, and hence

    gamma=(d-b0)/H in Z.

The main Pell root and its congruence are restored. For the unnormalized
strong source put I_old=Delta*I. Then

    I_old^2=Delta*(f^2-1),
    I_old=(2r_old+1)c^2,
    r_old=(Delta*(2r+1)-1)/2 in Z,

because a is even and hence Delta is odd. Also Q=I_old^2. The two auxiliary
quotients are explicitly

    o=f*(cT-R),  j_aux=(V+R)/c.

They are integers: V+c=f^2(cT-R)=f*o, and f^2=1 modc since
f^2=1+Delta*(2r+1)^2*c^4. These identities restore the auxiliary rows
V+c=f*o and V=c*j_aux-R, as well as
I_old^2 V^2-(I_old^2-1)y^2=1. The remaining first Pell row is exactly
tau^2=Dtau, and G,Z>0 provide the required sign witnesses. Thus every
zero yields a normalized source solution.

## Completeness

Start with the inherited canonical normalized source witness, with
Y=(2v_old+1)q^3, d=b0+H*gamma, and integral roots tau,f,d,y. Put
v=Y/q=q^2(2v_old+1). Its strict guards provide t with N>0.

The classical three-generalized-pentagonal theorem gives p2,p3,s with
24N-21=(6p2-1)^2+(6p3-1)^2+s^2. An elementary proof uses Legendre's
three-square theorem and the norm9 matrix in the fixed-prime source; it
does not restrict N beyond positivity.

Finally set

    n = gamma + 9tau + 3f + 27s + y - V - (v-q^2)/M.

This is an integer and makes (1) hold. One factor of F5 vanishes, so P=0.
We have proved both directions, with no assumption of consistency.

## Exact degree

The register degrees are

    q,W:1; X,Y:2; E,a,H:4; Delta:8; R,k:5; eta,zeta:7;
    Z:14; G:4; N,S:28; I:3; Df:14; Q,delta:22;
    V:19; Cy:60; M:2; U:6.

The five weighted roots have formal degrees 17,13,7,20,25 respectively.
The carrier has leading term UV, degree25. Since

    Cy/delta = V^2 + (V^2-1)/(Q-1),

one auxiliary-root branch is V plus a Laurent correction of degree -3.
After multiplication by U that correction has degree3. Sixteen norm
factors retain the auxiliary degree25; sixteen cancel it, and their unique
dominant term is the guard root of degree20. The denominator contributes
16*22. Thus degree is at most16*(25+20+22)=1072.

Writing leading homogeneous parts with subscript0, the top term is exactly

    Q0^16 (2 U0 V0)^16 (729 U0^2 S0)^8.

Here S0=-24 Z0^2 and Z0=-Y0^2 k0^2; none is zero. More explicitly, put
q0=6 beta*j, W0=12w, Y0=q0 v, a0=q0 W0 Y0, i0=2r,
R0=-q0^3(W0 C-q0 z), and k0=R0+h a0. Then the top form is

    2^136 3^56 q0^64 a0^128 i0^64 c^128 R0^16 Y0^32 k0^32.

In particular the coefficient of

    j^480 w^160 v^192 h^32 r^64 c^128 z^16

is 2^1000 3^696 beta^480 >0. Selection of h^32 uniquely selects (h a0)^32
from k0^32, and selection of z^16 selects (q0^4 z)^16 from R0^16.
The exponents sum to1072, proving the exact degree after specialization to
the actual nonzero fixed tuple.

## Assurance boundary

The proof establishes the new unbounded algebraic equivalence. The accompanying
checks establish literal circuit identities, degree attainment and coefficient
bindings. They do not establish consistency or the inherited compiler theorem.
No new Lean/Rocq or encoded object-ZFC proof is claimed.

## Three-operation norm simplification

In the first biquadratic squaring of the cleared norm, the coefficient vector
is exactly (q0,qt,qt,q3). Its square is

    (q0^2+(c+d)qt^2+cd*q3^2,
     2qt(q0+dq3), 2qt(q0+cq3), 2(q0q3+qt^2)).

These identities hold in every commutative ring. Factoring the repeated linear
coefficient before circuit construction saves three multiplications relative
to the generic four-component square, with identical output polynomial. The
new graph has 122 multiplications,39 additions,and34 subtractions.
