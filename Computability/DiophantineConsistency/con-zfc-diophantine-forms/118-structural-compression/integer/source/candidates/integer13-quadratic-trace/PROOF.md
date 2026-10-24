# Thirteen signed integers: trace with a quadratic main projection

This new endpoint retains the coherent six coefficients and thirteen
unrestricted integer unknowns of the frozen trace13 endpoint. It replaces
its main-root projection by a quadratic projection, removing that radical
from the norm. The conclusion is an ordinary two-way integer-solvability
reduction to the existing trace13 endpoint. Only after that restoration is
its named ordinary native/compiler/refutation calibration composed. No
Lean or encoded object-ZFC proof, consistency proof, or global minimum is
claimed.

## 1. Complete formula and source contract

Use precisely the trace13 definitions and coefficient tuple in the retained
`source/TRACE13_PROOF.md`. The unknowns are

    j,C,z,h,r,v,w,T,c,n,t,p2,p3 in Z.

The six ports are beta,K0,MC,MF,cone_A,cone_B from the single authentic
mixed-parity-unrounded-1064921 family. MF is already shifted once. Retain

    J=6j+1, q=beta J+1, W=12w+4, X=qW, Y=qv, E=XY,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    F=(K0+W)C-z(q-1),
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    i=2r+1, I=ic^2, Df=1+Delta I^2,
    Q=Delta^2 I^2, delta=Q-1,
    V=Df(cT-R)-c, Cy=QV^2-1,
    ell=XY^2, L=ell k, Dtau=1+L(L+k),
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Pair=G eta zeta-(t^2-G-eta zeta+1)^2,
    Ag=Pair-1-p2^2-p3(p3+1), M=2q^2, U=MH.

Set

    K=X(X+2ac)-1,
    Z=U(n+V)+MK+H(v-q^2).

The new polynomial is

    P=delta^8 F16(Z; U^2 Df,U^2 Dtau,U^2 Ag,U^2 Cy/delta),       (1)

where F16(x;A,B,E,D) is the product of
x-epsilon1 sqrt(A)-epsilon2 sqrt(B)-epsilon3 sqrt(E)-epsilon4 sqrt(D)
over all sixteen independent sign choices. The sign-invariant product
is an integer polynomial in its five displayed arguments. Its degree in
the last radicand is at most eight, so delta^8 clears all denominators.
The actual arithmetic DAG contains only integer leaves and +,-,* and is
defined at every integer tuple. Radicals and fractions below belong to the
proof of this polynomial, not to the permitted evaluation operations.

## 2. Uniform exceptional branches and trace before all inequalities

The frozen trace13 proof Sections2--3 establishes, independently of any
polynomial zero, guard, or native witness:

    q even, q=2 mod3, |q|>=16, |X|>=64,
    H odd and nonzero, Delta>=3,
    Df>=1, Dtau>=1, delta!=0, Dy=Cy/delta>=1.

This covers c=0 (Q=0,delta=-1,Dy=1) and v=0 (a=0,H=Delta=3).
Every rational root of Df,Dtau,Ag is integral since these are integer
radicands. Every rational root of Dy is integral by the adjacent-Pell
descent in that proof, including its separate Q=0 branch.

Suppose P=0. Since delta!=0 and U!=0, a complex norm factor gives
signed roots f,tau,g,y with

    Z=U(f+tau+g+y),                                          (2)

whose squares are Df,Dtau,Ag,Dy. Work in their finite multiquadratic
splitting field. Normalized trace fixes a rational root and sends an
irrational root to zero, since its quadratic minimal polynomial has zero
trace and field traces are transitive. Thus every root's normalized trace
is an integer. Apply normalized trace to(2): U divides Z. No individual
root is yet assumed rational; Ag is permitted to be negative here.

The exact identity

    Z=MH(n+V)+MK+H(v-q^2)

therefore gives M|H(v-q^2) and H|MK. As H=3 modq, q is not divisible
by3 and H is odd, gcd(H,M)=1. Consequently

    v=q^2(2s+1), s=(v-q^2)/(2q^2) in Z, H|K.                 (3)

Both congruences have been recovered before any sign or Pell-index
argument. In particular Y is nonzero and |Y|>=|q|^3>=4096. The v=0
branch is excluded by this argument, not by an extra multiplier in Ag.

## 3. Guard extraction and four-root separation

The other three radicands in(2) are positive. If Ag<0, its root would be
the only nonzero imaginary summand in a real equality. Thus Ag>=0, and

    Pair=Ag+1+p2^2+p3(p3+1)>0.

The elementary pair guard proves G>0 and eta*zeta>0, with no native
assumption. The latter excludes c=0, because there
eta*zeta=-Y(Y+1)k^2<=0. Thus Q>1 and delta>0 now hold.

Write x=|X|,m=|Y|,Kk=|k|,C0=|c|. The unchanged cubic-scale estimates
of trace13 Section5 give

    x>=64, m>=4096, Kk>=2,
    Kk(m-1)<C0<Kk(m+1), C0>30,
    tau>2C0, f>2tau, 0<=g<C0/10

for positive root magnitudes. The g bound follows from the exact
identity 12G=4q^2-[3(cone_A F+cone_B C)-4q]^2
-3(cone_A F-cone_B C)^2, hence G<=q^2/3, and eta*zeta<=k^2/4.
If cT-R=0 then C0<y<C0+1. Otherwise y>2f. After omitting g=0, these
orders are strictly superincreasing:

    cT-R=0:    g,y,tau,f;
    cT-R!=0:   g,tau,f,y.

For the first, g+y<1.1C0+1<2C0<tau; then f>2tau. For the second,
g<tau, g+tau<2tau<f, and g+tau+f<2f<y. A rational signed sum of such
roots forces every root rational: a Galois automorphism changing any
irrational sign would produce a nonempty vanishing signed subsum,
contradicting the strict hierarchy. Equation(2) therefore makes f,tau,g
integers, and y is integral by adjacent-Pell descent. This argument does
not require a sign for a+2,c,V,X,Y,H or any independence of square classes.

## 4. Signed main-root recovery before any main projection

Use the complete signed folding and bootstrap proof retained as
`source/SIGNED_QUADRATIC_PROOF.md`, Sections2,4,5. Its hypotheses here
are exactly the just-proved integral f,tau,y, the unscaled G>0 and
eta*zeta>0, and the cubic scale(3). That proof never uses a standalone
unit-product guard after these facts are available. The extra integral
g has no effect. We summarize the dependencies to make this application
explicit.

Let A=a+2,B0=|A|,I0=|I|,S0=Delta I0. The strong and auxiliary norms give

    f^2-(B0^2-1)I0^2=1,
    S0^2 V^2-(S0^2-1)y^2=1, V=-c modf.

Classify f=chi_B0(m0),I0=psi_B0(m0). The auxiliary index is odd since
S0 divides its chi coordinate; its odd-index polynomial modulo f gives
psi_B0(nu)=+C0 or -C0 modf. Folding all signed indices modulo2m0
produces 0<=p<=m0. Because C0<=I0 and 2I0<f, the congruence forces
C0=psi_B0(p),p>0, absorbing both signs of c and V. This recovers an
integral main norm, without assuming a main projection.

The inherited signed native and first-index prefix then yields p=R,
R=2r0+1 with r0>=24, and

    m>(x-3)^r0/2-1,
    |H|>2^(2R+2)x^2.                                       (4)

The prerequisite odd strong multiplier is Delta*i, not I itself:
r_old=(Delta*i-1)/2 is integral. No oddness of c is assumed. The proof
of(4) uses only the rank packing, strip bound, first Pell recurrence,
strong index divisibility and auxiliary step-down. It does not use H|K,
a sign of X, or a restored main congruence.

Put sigma=sign(c). Since R is odd, c=sigma psi_A(R). Signed polynomial
Pell projections give

    2^R K=(sigma X-2^R)(2^R sigma X+1) modH.

By(3), H divides this whole product. Its absolute value is less than
2^(2R+2)x^2<|H|. It is zero; the second factor cannot vanish because it
is odd and R>=1. Therefore sigma X=2^R. Taking

    d=sigma chi_A(R), b0=X+ac

recovers d^2=1+Delta c^2 and H|(d-b0). Define gamma=(d-b0)/H in Z.
This is a whole-product argument; no cancellation modulo composite H
or sign restriction on its modulus has been made.

## 5. Complete two-way integer existence maps

**New to old trace13.** Keep every coordinate except

    n_old=n+K/H+gamma.

This is integral. The old normalized center becomes the new center plus
d/H; thus(2) gives its five-root relation

    Z_old=M d+U(f+tau+g+y).

Its F32 norm vanishes. The private guard coordinates t,p2,p3 and the
physical Y and all six fixed ports are unchanged. No positivity of n is
needed.

**Old trace13 to new.** At an arbitrary old zero, the frozen trace13
theorem recovers integral f,tau,g,y,d with d^2=1+Delta c^2, H|(d-b0)
and the cubic scale. The exact identity

    b0^2-(1+Delta c^2)=K-Hc^2

gives H|K. Let s=(v-q^2)/M and choose the unrestricted integer

    n_new=f+tau+g+y-V-K/H-s.

Then the new normalized center is f+tau+g+y; one F16 factor vanishes.
Every retained guard and native quantity is unchanged. These maps prove
equivalence of integer-zero existence, not pointwise equality or a claimed
bijection of all witnesses. Composing only now with the old trace13
ordinary calibration gives the same ordinary consistency equivalence.
The separate missing encoded object-ZFC derivation is not supplied here.

## 6. Exact degree

The front degrees are delta22,U6,V19,Df14,Dtau22,Ag28,K7. Set

    A=U^2 Df, B=U^2 Dtau, Eguard=U^2 Ag, Cn=U^2 Cy,
    s0=Un+MK+H(v-q^2), Z=UV+s0.

Their degrees are26,34,40,72 and deg(s0)=9. In the quadratic ring
with e^2=Eguard, the cleared three-root norm at Z-e has components

    j0=delta(Z^2+Eguard-A-B)-Cn, j1=-2delta Z,
    T0=delta^2 A B, R0=delta Cn,
    k0=j0^2+Eguard j1^2-4[T0+R0(A+B)], k1=2j0 j1,
    f0=k0^2+Eguard k1^2-64T0R0(Z^2+Eguard),
    f1=2k0k1+128T0R0 Z,
    P=f0^2-Eguard f1^2.

The cancellation delta Z^2-Cn has degree at most56. Thus j0,j1 have
degrees62,47; k0,k1 have degrees134,109; f0,f1 have degrees268,243.
Their displayed unique top terms prove exact degree536, since
40+2*243=526<2*268. With a zero suffix denoting leading forms,

    P_top=2^8 Q0^8 U0^8 V0^8 Eguard0^4
         =2^56 q0^32 a0^64 i0^32 c^64 R0^8 eta0^16.

Here q0=6beta j,W0=12w,Y0=q0v,X0=q0W0,a0=X0Y0,i0=2r,
R0=-q0^3(W0C-q0z),eta0=-Y0(R0+h a0),U0=8q0^2 a0.
Selecting h^16 and z^8 gives the single coefficient

    [j^240 w^80 v^96 h^16 r^32 c^64 z^8]P
       =2^488*3^320*beta^240>0.

The exponent sum is536 and beta is the actual positive fixed numeral.
This is an exact attained degree, independently of the other five port
values. Finite sparse-ring and degree replays will check the circuit
transcription separately; they do not replace the unbounded proof above.
