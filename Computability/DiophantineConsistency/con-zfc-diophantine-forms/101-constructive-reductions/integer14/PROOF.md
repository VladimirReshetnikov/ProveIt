# Four Pell roots and a coprime carrier

## 1. Precisely stated result

The supplied polynomials have fourteen unrestricted integer unknowns:

    j, C, z, h, r, v, w, T, c, n, t, p2, p3, p1.

The centered polynomial has exact total degree 540 and 160 live binary
arithmetic operations. The simpler companion has exact degree 568 and 147
operations. A shared register is an abbreviation, not a quantified variable;
every gate is integer addition, subtraction, or multiplication. Coefficient
leaves and variable leaves are not charged as operations. These metrics do
not measure bit complexity, and no absolute minimum is asserted.

Both polynomials have an integer zero exactly when the normalized signed
native kernel of the retained parent has a zero. Composing with the parent's
explicitly identified ordinary compiler and K215/refutation calibration gives

    ZFC proves: (there is no integer zero) iff Con(ZFC).

This is an ordinary mathematical proof relative to the named imported ordinary
theorems. It is neither a proof of consistency nor a new end-to-end Lean/Rocq
certificate or exported object-language ZFC derivation. The retained parent
explains that latter formalization boundary in provenance/CALIBRATION_STATUS.md.
The new result is a smaller-degree equation at fourteen integer variables;
existing ten-integer high-degree equations remain separate alternatives.

## 2. Fixed coefficients and complete formula

Use exactly the six coefficients of upstream/coefficients/BINDING.json:

    beta = 2^1064921 - 1,
    K0, MC, MF = the complete source34 native tuple,
    cone_A = 2^1113, cone_B = 2^666104.

The MF port is already shifted by beta. The literal compressed integer bytes,
finite reconstruction, machine and tile data, source notices, and ordinary
calibration sources are retained under upstream. No coefficient is selected
by a consistency test or a halting search.

Define the following polynomial registers:

    J = 6j+1                  q = beta J+1
    W = 12w+4                 X = qW
    Y = qv                    E = XY
    a = E+Y                   H = 4a+3
    Delta = a^2+H             F = (K0+W)C-z(q-1)
    R = (q(q-F)-C)(q^2-1)+(MC+q MF)J
    k = R+1+hE                eta = c-Yk
    zeta = k-eta              i = 2r+1
    I = i c^2                 Df = 1+Delta I^2
    Q = Delta^2 I^2           delta = Q-1
    V = Df(cT-R)-c            Cy = Q V^2-1
    ell = XY^2                L = ell k
    Dtau = 1+ell(ell+1)k^2    Dmain = 1+Delta c^2
    b0 = X+ac                 F0 = (a+2)I.

For Pos(x,y,z)=1+x^2+y^2+z(z+1), set

    G = (cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Peta = eta zeta,
    B = v^2 G Peta-(t^2-v^2 G-Peta+1)^2-Pos(p1,p2,p3),
    S = B^2.

Let F16(x;A,B,D,C) be the product of

    x - eps1 sqrt(A) - eps2 sqrt(B) - eps3 sqrt(D) - eps4 sqrt(C)

over all sixteen independent sign choices. This product is an integer
polynomial in its five arguments, by sign invariance. The use of radicals
below abbreviates that polynomial, not operations allowed in the final DAG.

For the degree-540 polynomial put

    M = 4q^2,       U = MH,
    Z = U(n+2V+2L+k+2F0)+2M b0+2H(v-q^2),
    N = delta^8 F16(Z;4U^2 Df,4U^2 Dtau,4M^2 Dmain,4U^2 Cy/delta),
    P540 = N+S+NS = (1+S)(1+N)-1.

The factor delta^8 clears the denominator symbolically. This is an ordinary
polynomial, even at delta=0 as a formal input. Section 4 proves that delta
never vanishes on the actual integer domain of the front end.

For the degree-568 companion instead use

    M = 2q^2, U = MH,
    Z = U(n+V)+M b0+H(v-q^2),
    N = delta^8 F16(Z;U^2 Df,U^2 Dtau,M^2 Dmain,U^2 Cy/delta),
    P568 = N+S+NS.

All other registers, including the same guard B, remain unchanged.

## 3. The unit-product finalizer and the guard

If N,S are integers and S>=0, (1+S)(1+N)=1 forces S=N=0: the first
factor is a positive integer divisor of 1. Hence P540=0 and P568=0 are
respectively equivalent to B=N=0. No positivity claim about N is needed.

For arbitrary integers x,y,t define

    Pair(x,y,t)=xy-(t^2-x-y+1)^2.

There exists t with Pair>0 if and only if x>0 and y>0. Indeed Pair>0
implies xy>0; if x=-u,y=-v with u,v>0, its subtracted square is at least
(u+v+1)^2>uv, a contradiction. Conversely, for x,y>0, put K=x+y-1.
Choosing an integer t whose square is nearest K gives
(t^2-K)^2<K<=xy. To verify the strict bound, between m^2 and (m+1)^2
the nearest-square error is at most m, whose square is less than K;
at square endpoints the error is zero. The endpoint K=1 is immediate.

Pos represents exactly the strictly positive integers. Its values are
positive, and Legendre's three-square theorem applied to 4n-3 gives an
odd square and two even squares, hence n=1+x^2+y^2+z(z+1).

Thus B=0 implies v!=0, G>0, eta*zeta>0. Conversely those three inequalities
admit witnesses t,p1,p2,p3 making B=0. This is an existential equivalence;
the private guard witnesses are chosen anew when necessary.

## 4. Exceptional branches and weak-scale estimates

Because beta is odd and beta=1 modulo 3, q=beta(6j+1)+1 is even,
q=2 modulo 3, and |q|>=16. Also W=4(3w+1) is nonzero, so
x=|X|>=64. If v=0, then a=0, H=3, Delta=3. If v!=0, then
m=|Y|>=16 and |a|>=63*16, so Delta=(a+1)(a+3)>0. In all cases H!=0,
Delta>=3, and Dmain,Df,Dtau are positive. For Dtau use the elementary
integer inequality ell(ell+1)>=0, also for negative ell.

If c=0 then Q=0, delta=-1, Cy=-1, and Cy/delta=1. If c!=0, Q>=9,
Df>|c|+1, and V=Df b-c with integer b=cT-R has |V|>=1. Consequently
Cy/delta=V^2+(V^2-1)/(Q-1)>=1. In particular delta is never zero.
These statements require no Diophantine equation or guard assumption.

At a polynomial zero B=0. Put K=|k| and C0=|c|. Since eta,zeta have one
strict nonzero sign, K>=2 and eta/k lies strictly between 0 and 1. Therefore

    K(m-1)<C0<K(m+1),       C0>30.

In particular c!=0 and delta>0. These estimates use only Y=qv, not the
stronger cubic-scale congruence that will be recovered later.

Write d=sqrt(Dmain), f=sqrt(Df), tau=sqrt(Dtau), y=sqrt(Cy/delta)
for the positive real roots. The following estimates hold:

    d/|H|<C0/2,   tau>2C0,   f>2tau.

For the first, H^2-4Delta=12a^2+8a-3 and |a|>=1008 imply
H^2 C0^2>4(Delta C0^2+1). For the second,
K(xm^2-1)<tau<K(xm^2+1), and xm^2-1>2(m+1).
For the third, sqrt(Delta)>|a|-3 gives

    d>((x-1)m-3)K(m-1)>3tau/4.

The second inequality follows by expanding
4((x-1)m-3)(m-1)-3(xm^2+1)
=m^2(x-4)-4m(x+2)+9>0 for x>=64,m>=16. Also
f>(C0/2)d>15d, which implies f>2tau.

Furthermore f>3C0^2 and Q>f^2. If b=cT-R=0, then

    C0<y<C0+1.

If b!=0, then |V|>=f^2-C0>2f and therefore y>|V|>2f.
It follows that the four root magnitudes are strictly superincreasing in
one of these descending orders:

    b=0:   f, tau, y, d/|H|;
    b!=0:  y, f, tau, d/|H|.

Here every entry exceeds the sum of all later entries. For example in the
first case y+d/|H|<1.5C0+1<2C0<tau, and then f>2tau. The second case
follows from y>2f, f>2tau, and tau>2C0>d/|H|.

This is the reason the old amplifier 4H+1 can be deleted: after the guard
root is retained explicitly, it is no longer one of the radicals requiring
separation. The four remaining roots have the required order at the weak
scale Y=qv itself.

## 5. Radical extraction, rational descent, and CRT

For positive numbers with rational squares and strictly superincreasing
magnitudes, a rational signed sum forces every summand to be rational.
Indeed, if any root were irrational, a Galois automorphism of their
multiquadratic extension would change at least one sign. Subtracting the
automorphic image of the rational sum produces a nonempty vanishing signed
subsum, impossible because its largest magnitude exceeds all the others.
No independence of the radicands' square classes is assumed.

At N=0, a conjugate factor vanishes. Divide by 2U in the centered form,
or by U in the companion. The preceding argument gives rational roots
d,f,tau,y. The first three are integers because their squares are integers.
The auxiliary y is integral by the following elementary descent:

If Q>1,V are integers and QV^2-(Q-1)y^2=1 with rational y, then y is an
integer. Write |y|=a/b in lowest terms, so b^2 divides Q-1. The map

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserves the equation, preserves b, and keeps V' integral. For V>1,
y>V and (Q-1)y<QV imply -V<V'<V. The equation excludes V'=0.
Taking absolute values and descending reaches |V|=1, where |y|=1,
so b=1. Signs cause no difficulty.

Absorb the conjugate signs into the integer roots. For the centered form,

    Z=2M d+2U(f+tau+y).

Because H=4(X+1)qv+3, H=3 modulo q. Since q=2 modulo 3 and H is odd,

    gcd(H,4q^2)=1.

Reducing the factor equality modulo M=4q^2 yields
M divides 2H(v-q^2), and hence 2q^2 divides v-q^2. Thus

    v=q^2(2v_old+1),    Y=(2v_old+1)q^3.

Reducing modulo H gives H divides 2M(d-b0), hence

    gamma=(d-b0)/H is an integer.

These are the missing cubic scale and main Pell congruence. The simpler
companion uses M=2q^2 and no factors 2, and gives exactly the same two
congruences.

## 6. Two-way existence equivalence and calibration

All recovered normalized roots obey

    f^2=1+Delta i^2c^4,
    tau^2=1+XY^2(XY^2+1)k^2,
    (b0+H gamma)^2=1+Delta c^2,
    QV^2-(Q-1)y^2=1.

Together with Y=(2v_old+1)q^3, G>0, eta*zeta>0, and the identical native
registers, these are precisely the parent's normalized signed kernel.
Its private Pos guard witnesses may be regenerated from G>0 and eta*zeta>0.
The original strong-kernel coordinates have the explicit restoration

    I_old=Delta i c^2,       r_old=(Delta i-1)/2,
    o_old=f(cT-R),
    j_old=Df T-1-R Delta i^2 c^3.

Delta*i is odd, so r_old is integral. Direct substitution gives
I_old^2=Delta(f^2-1)=Q, f o_old-c=V, and c j_old-R=V.
These are also the maps proved in upstream/report/report.tex, the displayed restoration equations
in its normalized-kernel section. The first centered Pell root is
tau-XY^2k, and the transport identity is built into F.

Conversely, start with a source normalized kernel witness, or choose the
canonical witnesses from the parent's completeness theorem. Set
v=q^2(2v_old+1), retain every core coordinate, and choose t,p1,p2,p3
so Pair(v^2G,eta*zeta,t)=Pos(p1,p2,p3). This is possible by Section 3.
For the centered form choose the integer

    n=2(gamma+f+tau+y-V-L-F0)-k-(v-q^2)/(2q^2).

For the companion choose

    n=gamma+f+tau+y-V-(v-q^2)/(2q^2).

Each displayed quantity has already been defined; no circular choice occurs.
The selected conjugate factor is zero, the guard is zero, and hence P is zero.
This proves the new two-way existence reduction.

The ordinary semantic calibration is imported from the retained parent:
its normalized kernel exists iff the source34 canonical/native K215 language
has an accepting witness, iff the literal K215 blank run halts, iff the
specified recursive ZFC calculus has a finite refutation. The parent supplies
its ordinary proof sources, source pins, and canonical odd-strong-witness
construction. Those arguments are stated as mathematics formalizable in ZFC.
Composing them with this elementary algebraic reduction and negating gives
the asserted no-solution/Con(ZFC) equivalence. The missing end-to-end encoded
formalization is not inferred from finite computations or an external theorem.

## 7. Exact degree of the centered form

Use total degree in the fourteen variables, treating the fixed coefficients
as degree zero. A subscript 0 denotes the highest homogeneous part. Put

    q0=6 beta j, W0=12w, X0=q0 W0, Y0=q0 v,
    a0=X0 Y0, i0=2r,
    R0=q0^4 z-q0^3 W0 C,
    k0=R0+h a0, eta0=-Y0 k0,
    Q0=a0^4 i0^2 c^4,
    V0=-a0^2 i0^2 c^4 R0,
    L0=X0 Y0^2 k0,
    F00=a0 i0 c^2,
    U0=16q0^2 a0.

The degrees of delta,U,V,L,F0,eta are respectively 22,6,19,11,7,7.
The guard B has top part -eta0^4, so S has top part eta0^8 and degree 56.

The degree of the cleared four-root norm can be computed without expanding
it. Let the approximate roots be

    ry=2UV, rt=U(2L+k), rf=2UF0, rd=2M b0,
    s=Un+2H(v-q^2),   Z=ry+rt+rf+rd+s.

The exact defects are

    4U^2 Cy/delta-ry^2 = 4U^2(V^2-1)/delta,
    4U^2 Dtau-rt^2 = U^2(4-k^2),
    4U^2 Df-rf^2 = 4U^2(1-I^2),
    4M^2 Dmain-rd^2 = 4M^2(1+Hc^2-2acX-X^2).

The approximate root degrees are 25,17,13,7. The correction degrees in
their formal square roots are respectively at most 3,5,5,4. To make this
rigorous, substitute every variable by a new indeterminate u times that
variable and work in the Laurent-series field over the rational function
field in the original variables. Each radicand is its approximate-root
square times 1 plus terms of negative u degree, so its formal square root
with that leading sign exists by the binomial series. Only its leading
degree is needed; no infinite expression is part of the delivered polynomial.

Among the sixteen factors, eight have degree 25 (the y sign is negative),
four have degree 17, two have degree 13, and the final two have degree 7.
The latter leading terms are U0*n and U0*(n+c): s0=U0*n, and
2rd0=4M0*a0*c=U0*c. Hence the product degree is
8*25+4*17+2*13+2*7=308. The clearing factor delta^8 adds 176.
Thus N has exact degree 484, with highest homogeneous part

    2^28 U0^16 Q0^8 V0^8 L0^4 F00^2 n(n+c).

No one of these factors is the zero polynomial on the actual coefficient
slice. Multiplication by S dominates the lower-degree N and S summands.
Therefore the complete degree-540 part is

    2^28 U0^16 Q0^8 V0^8 L0^4 F00^2 eta0^8 n(n+c).

Selecting h^12 from k0^12, z^8 from R0^8, and n^2 from n(n+c) gives

    [j^240 w^82 v^94 h^12 r^34 c^68 z^8 n^2] P540
        = 2^530 3^322 beta^240 > 0.

The displayed exponents sum to 540. This proves exact degree for the
actual six fixed integers, independently of numerical coincidence among
the other five coefficients.

## 8. Exact degree of the simpler companion

Write its center as Z=UV+s with s=Un+M b0+H(v-q^2), of degree 7.
Only the y radical is centered. Its correction has degree at most 3;
the other radical root degrees are 17 (tau),13 (f),7 (main).
Eight conjugate factors have leading degree 25 and the remaining eight
have leading degree 17, dominated by the signed tau root. Thus the
factor product has degree 336 and delta^8 makes degree 512. Its leading
form is

    2^8 U0^16 Q0^8 V0^8 L0^8,

where now U0=8q0^2 a0. The guard remains degree 56, so the single
polynomial has exact degree 568. More explicitly,

    [j^256 w^88 v^104 h^16 r^32 c^64 z^8] P568
        = 2^520 3^344 beta^256 > 0.

Every norm factor argument and both restoration maps are already proved
above; this companion adds no independent semantic assumption.

## 9. Comparison and verification scope

The incoming fixed-prime package has a fourteen-integer polynomial of exact
degree 652 and 230 operations; the incoming root-fusion package also gives
fourteen integers at degree 696 and 150 operations, or 792 and 137 operations.
The new 540/160 and 568/147 choices improve those degree slices and are
tradeoffs with each other. The 568/147 choice strictly improves 696/150 in
both degree and circuit size. The existing 792/137 alternative still has a
smaller operation count. A world priority or global optimum is not claimed.

verify.py checks exact equality of the generic norm's entire coefficient
list against an independent conjugate product, the four defect identities,
leading homogeneous coefficients, actual coefficient payload hashes, DAG
rebuilding and liveness, and finite modular transcription diagnostics.
Those finite checks support the exact algebra, not the unbounded semantic
compiler theorem. Source ordinary proofs and licenses remain in upstream.
