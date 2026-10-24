# Signed main-root elimination by a quadratic projection

This is a new ordinary arithmetic reduction from the frozen
`constructive-integer14-shared` endpoint. It does not silently transfer a
positive-domain theorem. All fourteen coordinates remain unrestricted
integers, and the six original coefficients are retained. Native/compiler
calibration is inherited only after an old integer zero has been restored.
No Lean or internal-ZFC derivation is claimed.

Use the definitions of `source/parent/PROOF.md`, the constructive
integer14 degree568 companion: q,W,X,Y,a,H,Delta,F,R,k,c,I,Df,Q,delta,V,
Cy,Dtau and the guard B are unchanged. Write

    A=a+2, H=4a+3=4A-5, Delta=A^2-1,
    b0=X+ac, M=2q^2, U=MH.

The sign of A, X, Y, c, I, V and H is not assumed. In particular the
projection proof below works before any orientation has been recovered.

## 1. The changed polynomial

Replace the main-root projection term b0 by

    K=X(X+2ac)-1,
    Z=U(n+V)+M K+H(v-q^2).

Define four polynomial arguments

    s=delta Z^2,
    u=delta U^2 Df,
    t=delta U^2 Dtau,
    w=U^2 Cy.

Let F8 be the octic three-root norm from the positive quadratic-projection
proof, or equivalently its symmetric form

    F8(s;u,t,w)=[(s+w-u-t)^2-4(sw+ut)]^2-64swut.

Set N=F8(s;u,t,w), keep S=B^2, and use the single equation

    P=N+S+NS=0.

At a zero, the integer unit-product argument makes B=N=0 even if N is
negative off the zero set. The unchanged guard therefore gives v!=0,
G>0 and eta*zeta>0. It follows from the weak-scale estimates in the
parent proof that c!=0, delta>0, H!=0 and U!=0. The norm identity becomes

    N=delta^4 U^8 product_eps
       (Z/U-eps1*f-eps2*tau-eps3*y),                         (1)

where f=sqrt(Df), tau=sqrt(Dtau), y=sqrt(Cy/delta) are positive real
numbers. The prefactor is nonzero. This is an exact denominator-cleared
polynomial identity; no division or radical is an operation in the DAG.

## 2. Extraction and signed main classification at the weak scale

The parent weak-scale estimates, which require only Y=qv, give the same
three-root separation after the main root is removed:

* if cT-R=0, then |c|<y<|c|+1<tau and f>2tau;
* otherwise y>2f and f>2tau.

Thus no nonempty signed subsum of f,tau,y vanishes. A rational signed
sum in(1) makes all three roots rational by the multiquadratic Galois
argument. Integral squares make f,tau integers, and the parent adjacent
Pell descent makes y an integer. Neither V>0 nor a sign of A was needed.

Put B0=|A|, C0=|c| and I0=|I|. The guard and weak-scale bounds give
B0>=3, C0>30 and I0=|2r+1|C0^2>=C0. Hence

    f^2-(B0^2-1)I0^2=1, f>2I0,
    S0=(B0^2-1)I0, Q=S0^2,
    QV^2-(Q-1)y^2=1, V=-c modulo f.

Classify the last equation as

    S0|V|=chi_S0(nu), y=psi_S0(nu), nu>=1.

The recurrence gives chi_S0(even)=+1 or -1 modulo S0; since S0>=2
and S0 divides chi_S0(nu), nu=2h+1 is odd. The polynomial identity
chi_Z(2h+1)=Z Q_h(Z^2), together with
Q_h(1-B0^2)=(-1)^h psi_B0(2h+1), shows

    psi_B0(nu)=+C0 or -C0 modulo f.                          (2)

Here both signs of V and c have been absorbed, not discarded. Write the
strong pair f=chi_B0(m0), I0=psi_B0(m0), m0>=1. Since
alpha^(2m0)=-1 modulo f, psi_B0(nu) folds to +psi_B0(p) or
-psi_B0(p) modulo f for some0<=p<=m0. This holds for all integer
indices: reduce modulo2m0 and use psi(2m0-j)=psi(j) modulo f.

Now0<=psi_B0(p)<=I0 and I0+C0<=2I0<f. Equation(2) therefore forces
psi_B0(p)=C0; the opposite sign would put a positive multiple of f
strictly between0 and f. Since C0>0, p>=1. In particular the omitted
main norm really does have an integer root. No positivity of c or A
has entered this classification.

## 3. Cubic scale is recovered before the signed index bootstrap

The factor equation in(1), divided by U, says

    n+V+K/H+(v-q^2)/M = eps1*f+eps2*tau+eps3*y.              (3)

As in the parent, H is odd, H=3 modulo q and q=2 modulo3. Thus
gcd(H,M)=1, also for negative H or q. Reduction of the integral factor
equation modulo M and H gives respectively

    M | v-q^2, H | K.

Consequently v=q^2(2v_old+1) and Y=(2v_old+1)q^3. This scale is
licensed before using any signed ratio or strong-index argument. Let
ell0=(v-q^2)/M be the recovered integer.

## 4. Signed rank and ratio facts used before projection

We use the already reviewed signed-bootstrap prefix in the retained
`RESIDUE_AND_DETERMINANT.md`, Section4, **only up to its projection
argument**. Its hypotheses here follow from the guard, the recovered
cubic scale and the main classification just proved. For clarity, the
relevant argument and its dependencies are restated.

The determinant G>0 recovers the common strict sign of F,C,q and of
alpha=q-F-C. The authentic masks then give, for Q0=|q|>=16,

    Q0(Q0^2-1)<R<Q0^4-2.

This packing bound does not use X's sign or a main projection. Let
x=|X|>=4Q0>=64 and m=|Y|>=Q0^3. Then |E|=xm>3R+1.
With K0=|k|, the eta*zeta guard gives

    K0(m-1)<C0<K0(m+1), C0>K0.

The positive first Pell parameter is P0=|2XY^2+1|, even when X<0.
Thus K0=2psi_P0(n0), n0>=1. Since P0>B0 and C0=psi_B0(p)>K0,
monotonicity gives p>n0. Modulo |E| the first recurrence and the index
definition k=R+1+hE give

    2n0=epsilon(R+1) modulo |E|,
    epsilon=sign(k)*sign(X)^(n0-1).

If epsilon=-1 then n0>R; otherwise n0>=(R+1)/2. In either case
p>n0>=24, so ordinary Pell growth gives
C0>B0(B0^2-1)^2, C0>2p and C0>2R.

The unchanged ordinary strong-rank lemma, applied to
f^2-(B0^2-1)I0^2=1 with C0^2|I0, gives C0|m0 and m0>2p.
The signed auxiliary step-down needs exactly

    S0^2=(B0^2-1)(f^2-1), C0|S0,
    V=-c modulo f, V=-R modulo C0,
    S0^2 V^2-(S0^2-1)y^2=1.

These hold from V=f^2(cT-R)-c and f^2=1+Delta i^2c^4. Its squared
index congruence is unchanged by either sign of c or A, and yields
R=+p or -p modulo C0. The strict bounds0<R,p<C0/2 give p=R.
The epsilon=-1 first-index branch is then impossible. In the other
branch both2n0 and R+1 are below |E|, so2n0=R+1.

Write R=2r0+1 with r0>=24. The same sign-uniform ratio estimate gives

    C0/K0 >= (1/2)*[(2B0-1)^2/(2P0)]^r0,
    m>(x-3)^r0/2-1.                                         (4)

Indeed B0>=(x-1)m-2, P0<=2xm^2+1, and the cleared base difference
is strictly positive for x>=64,m>=6, as proved by the positive-coefficient
identity in that signed-bootstrap source. Combining the ratio with
C0/K0<m+1 gives(4). No step in this section used H|(d-b0) or a sign
for X,Y,A,c. For the original strong-kernel coordinate change, the
multiplier Delta*i is odd: q is even, so Y and a are even and Delta is
odd, while i=2r+1 is odd. Therefore r_old=(Delta*i-1)/2 is an integer
and I_old=(2r_old+1)c^2=Delta*i*c^2. No oddness of I_old or c is assumed;
these normalized restorations satisfy the same inherited signed lemma.

## 5. The signed whole-product bound

The absolute value of H satisfies

    |H|>=4(x-1)m-3>3xm>x(x-3)^r0.                           (5)

The last inequality uses(4) and (x-3)^r0>6. For x>=64 and r0>=10,

    (x-3)^r0 >= (x/2)*61^(r0-1)
                  > x*2^(5r0-6) >= x*2^(4r0+4).

Thus our actual r0>=24 implies

    |H|>2^(2R+2)x^2.                                       (6)

Let sigma=sign(c). Because R is odd,
psi_A(R)=psi_|A|(R)=C0, so c=sigma psi_A(R). The signed polynomial
Pell projections modulo odd H are

    chi_A(R)-a psi_A(R)=2^R,
    chi_A(R)+a psi_A(R)=2^(-R).

They follow from the recurrence also for negative A; they were already
used in the retained signed-bootstrap proof. Put Z0=sigma X, so
K=Z0^2+2a psi_A(R)Z0-1. It follows that

    2^R K=(Z0-2^R)(2^R Z0+1) modulo H.                     (7)

Since H|K, H divides the whole product in(7). Its absolute value is
strictly less than2^(2R+2)x^2<|H|: each factor is bounded by
2^(R+1)x, whether Z0 is positive or negative. Therefore the product
is0. The second factor cannot vanish, since2^R Z0+1 is odd and R>=1.
Hence Z0=2^R, or

    sigma X=2^R.                                           (8)

This is a whole-product argument. It neither assumes a positive root
sign nor cancels a nonunit modulo a composite H. Define
d=sigma chi_A(R). Then d is a signed integer root of Dmain and,
by(8), H|(d-X-ac). Put gamma=(d-b0)/H. This restores the exact
main projection of the old integer kernel. No later orientation or
compiler theorem has been used to obtain it.

## 6. Complete two-way maps of integer zero existence

**New to old.** Keep every unknown except set

    n_old=n+K/H+gamma.

This is an integer; n is unrestricted. The old normalized center is
the new one plus d/H. Equation(3) therefore makes an old four-root
factor vanish. The unchanged guard is zero, so the old unit-product
output is zero. Its original ordinary theorem can now be applied.

**Old to new.** At an arbitrary old zero, the original extraction and
CRT give integral roots f,tau,y,d, gamma=(d-b0)/H and
ell0=(v-q^2)/M. Since d^2=Dmain, the exact identity

    b0^2-Dmain=K-Hc^2

shows H|K. Retain every other unknown and choose the unrestricted
integer

    n_new=f+tau+y-V-K/H-ell0,

using the positive magnitudes f,tau,y. The normalized new center is
then f+tau+y, so a three-root factor vanishes. The guard is unchanged
and the new output is zero. There is no positivity requirement on this
new n and no circular witness choice.

This proves equivalence of integer-zero existence with the frozen old
endpoint, not pointwise equality or a zero-set bijection. Only then is
the inherited native/refutation theorem composed. In particular no
positive-domain calibration or coherent tuple is exchanged for another.

## 7. Degree and nonzero leading form

The old leading notation remains: delta22,U6,V19, Dtaufirst-root11,
Dfroot7, eta7. Replacing b0 of degree5 by K of degree7 makes
Z-UV have degree9, still below the uncentered tau-root degree17.

Equivalently, in the new scaled arguments, deg(s)=deg(w)=72,
deg(u)=48, deg(t)=56, and omega=s-w has degree56. The uncentered
syntactic bound is288 for N. In the symmetric octic expression its
inner form has leading part -4t0*w0, of degree128: the equivalent
original form is

    [(omega-u-t)^2-4(ut+(u+t)w)]^2-64utws.

The first bracket's square term has degree at most112, whereas tw
has degree128. Its leading coefficient is therefore nonzero, and
the remaining product utws has degree248<256. Thus N has exact
degree256, with leading form

    16 Q0^4 U0^8 V0^4 L0^4.

The guard S has degree56 and leading eta0^8, so P has exact degree312
and leading16 Q0^4 U0^8 V0^4 L0^4 eta0^8. Selecting h^12 and z^4
as in the parent's leading-form proof yields

    [j^140 w^48 v^60 h^12 r^16 c^32 z^4] P
        =2^280*3^188*beta^140>0.

The exponent sum is312 and the actual beta is positive. Exact degree
does not rest on generic-specialization heuristics or finite samples.
Literal operation counts and independent finite symbolic/degree controls
are supplied separately when the materialized circuit is sealed.
