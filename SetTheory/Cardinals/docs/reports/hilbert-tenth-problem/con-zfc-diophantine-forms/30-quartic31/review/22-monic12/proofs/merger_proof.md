# A monic-polynomial merger: twelve positive unknowns

## Scope and dependency

This is a reduction from the blank-input normalized Pell/compiler interface of
package 09 (and its signed-gamma extension proved in package 12). All four fixed
coefficient ports must come from one authenticated compiler tuple. The new
argument is ordinary mathematics formalizable in ZFC, not a new proof-assistant
theorem. The underlying statement is existence of a positive solution iff the
literal blank K215 machine halts. The K215 calibration then gives the requested
equivalence with syntactic ZFC inconsistency.

All twelve supplied coordinates

    J, F, alpha, z, h, i, T, s, w, eta, zeta, u

are strictly positive integers. All other symbols below are polynomial
abbreviations. The four fixed ports are beta=Bbase-1, K0, MC, and the shifted MF.

## Common definitions

    q = beta J + 1
    C = q - F - alpha
    X = wq, Y = sq^3, E = XY
    k = eta + zeta, c = kY + eta, a = E+Y
    H = 4a+3, Delta = a^2+H = (a+2)^2-1
    G = (q-1)(q-F)+alpha
    R = G(q^2-1) + (MC+q MF)J
    L0 = E(kY), A = 1+L0(L0+k)
    Nk = k-hE-R
    Nt = (K0+w)C+(q-F)-z(q-1).

For the normalized strong root set

    I = i c^2, D = 1+Delta I^2, Q = Delta(D-1), d=Q-1
    v0 = cT, b = c+RD
    P = Q D v0^2, Z = Q b^2, e=P+Z-1, a0=PZ
    M = 2(kI^2+T^2), N=dM^2 A.

Thus Q=(Delta i c^2)^2 is a square and Q>1. The weight is twice
package 09's low-degree weight. The factor 2 is convenient for a strict
nonzero-root bound; it does not change any degree.

Introduce the monic degree-eight polynomial in an auxiliary indeterminate v:

    H8(v) = [v^4 - 2d(N+e)v^2 + d^2((N-e)^2+4a0)]^2
            -16a0 d^2[v^2+d(N-e)]^2.

The indeterminate v is eliminated and is not a supplied unknown. Define

    B = 1+Delta c^2, W = X+ac+Hu, p=Hc
    R12 = Res_v(H8(v), (W-pv)^2-B).

The resultant is an ordinary fixed polynomial. An explicit division-free
circuit for it is given below; no resultant evaluation or algebraic-number
primitive is needed to evaluate that circuit.

The proposed three-equation system is

    Nk=1, Nt=1, R12=0.

The proposed single equation is

    P12 = Nk Nt(1+R12)-1 = 0.

Its exact total degree is 1529. The system has maximum degree 1520.

## Explicit norm circuit for the resultant

Arithmetic in the quadratic algebra Z[sqrt(B)] can be done with pairs.
Put

    r0 = W^2+B, r1=2W, dp2=d p^2, d2p4=(dp2)^2
    S=N-e, ell=2 dp2(N+e)
    vc=d2p4(S^2+4a0)
    vR=r0^2+B r1^2-ell r0+vc
    vI=r1(2r0-ell)
    uR=r0+dp2 S
    coef=16a0 d2p4
    hR=vR^2+B vI^2-coef(uR^2+B r1^2)
    hI=2(vR vI-coef uR r1)
    R12=hR^2-B hI^2.

The exact identity in the quadratic algebra is

    hR+hI sqrt(B) = p^8 H8((W+sqrt(B))/p).

Since p>0, multiplying the two conjugates gives precisely the displayed
resultant, with no extra zero factor. This statement also follows from the
root formula for a resultant; the second polynomial has leading coefficient
p^2, and H8 has degree 8.

## Lemma 1: extracting the main square from a monic witness

Let a,c be positive integers, Delta=(a+2)^2-1, H=4a+3,
B=1+Delta c^2, and W an integer. Suppose a monic integer polynomial Hn has a
common complex root v with (W-Hcv)^2-B. Then B is an integer square, v is an
integer, and gamma=u-cv is an integer whenever W=X+ac+Hu.

Proof. The common root is v=(W+/-sqrt(B))/(Hc), so it is real. Monicity
makes v an algebraic integer. If B is not a square, v has conjugate
v'=(W-/+sqrt(B))/(Hc); v-v' is a nonzero algebraic integer. Its norm is

    -4B/(H^2 c^2).

But H^2-4Delta=12a^2+8a-3, so H^2 c^2-4B>0 for a,c>=1.
This norm lies strictly between -1 and 0, contradicting the integrality of
the norm of an algebraic integer. Hence B is a square, v is rational, and a
rational algebraic integer is an integer. Consequently gamma=u-cv is
integral. The common-root equation is exactly

    (X+ac+H gamma)^2-Delta c^2=1.

This argument is the new merger. It encodes the main Pell root and its
congruence quotient without retaining a separate gamma variable.

## Lemma 2: a rational auxiliary coordinate is automatically integral

Let S>=2 and V be integers. If y is rational and

    S^2 V^2-(S^2-1)y^2=1,

then y is an integer.

Proof. Write S^2-1=b0^2 D0 with D0 positive squarefree. It is nonsquare,
since S^2-1 is not an integer square. Put x=S|V| and z0=b0|y|. The
equation is x^2-D0 z0^2=1. Squarefree valuations force the rational z0
to be integral: a reduced denominator squared would have to divide D0.

Let F+G sqrt(D0) be the fundamental positive unit with integer
coefficients, and define chi_F and psi_F by

    (F+sqrt(F^2-1))^n=chi_F(n)+psi_F(n)sqrt(F^2-1).

Ordinary Pell classification gives positive integers e0,m with

    S=chi_F(e0), b0=G psi_F(e0),
    x=chi_F(m), z0=G psi_F(m).

The crucial divisibility fact is

    chi_F(e0) | chi_F(m)  ==>  m/e0 is an odd integer.

Here is an elementary proof. The addition identities give

    chi_F(m+2e0) == -chi_F(m) mod chi_F(e0)
    chi_F(2e0-r) == -chi_F(r) mod chi_F(e0).

Reduce m modulo 2e0 and reflect to 0<=r<=e0. For r<e0,
1<=chi_F(r)<chi_F(e0), which is incompatible with divisibility.
Therefore r=e0, as claimed. The usual multiplication identity now gives
psi_F(e0)|psi_F(m). Finally

    |y|=psi_F(m)/psi_F(e0)

is integral. This proves saturation without assuming the auxiliary
discriminant is squarefree.

## Lemma 3: restoring the eliminated roots from rational t

Put

    C_t=d t^2+N-e
    U_t=C_t^2+4(a0-d t^2 N)
    R_t=U_t^2-16 C_t^2 a0.

The identity

    H8(d t)=d^4 R_t

holds by direct expansion. The low-degree weight estimate proved in package
09 gives d(kI^2+T^2)^2 A>e+1 under the outer unit bounds
Nt,Nk in {+1,-1}. Doubling the weight therefore gives N>4(e+1).
For clarity, the inherited estimate uses k>E, R<k, c<2kY,
A0=a+2<2E, L0>A0 c/4, L0>4A0^2, and D<A0^2I^2.
These bounds hold before any eliminated square roots are recovered.

Suppose t is rational and R_t=0. Then C_t>0. Also t cannot be zero:

    R_0=[(N-e)^2-4a0]^2,

where 2sqrt(a0)<=P+Z=e+1<N-e. Thus R_0>0.
Let B0=2Q v0 b, which is positive. Since 4a0=D B0^2,

    f=-U_t/(2 C_t B0)

is rational with f^2=D, hence is a nonzero integer. The same identity gives

    (C_t+B0 f)^2=4d^2 t^2 M^2 A.

Therefore tau=(C_t+B0 f)/(2dtM) is rational with tau^2=A, hence is an
integer. Set y=t-M tau. Then y is rational and

    Q(v0 f-b)^2-(Q-1)y^2=1.

Since Q is an integer square and V=v0f-b is an integer, Lemma 2 makes y
an integer. It follows also that t=M tau+y is an integer. This restores
all three roots f,tau,y; none was assumed integral during elimination.

## Soundness and completeness of the twelve-variable system

At a system solution, the resultant has a common root v. Lemma 1 gives
integer v and gamma=u-cv satisfying the main norm. Apply Lemma 3 to
t=v/d. The restored integers satisfy the normalized strong equation,
first norm and auxiliary norm, together with Nk=Nt=1. The only relaxed
signs are gamma and the restored roots. Absolute values fix tau and y.
If f<0, change signs of both f and T, preserving Tf. Set
i_ordinary=Delta i; then (i_ordinary c^2)^2=Delta(f^2-1)=Q,
so the ordinary auxiliary coefficient is exactly the restored Q. The signed-gamma,
signed-T arithmetic theorem of package 12 then gives the same blank
halting computation. That theorem proves gamma>0 as a consequence:
the negative main Pell root contradicts its congruence modulo H, and
the positive root has root-ac>X. Its proof is the section headed
"The main root sign and the power of two" in 12-gap-norm14/report.tex.

Conversely, take a canonical positive normalized blank compiler solution.
Set M=2(kI^2+T^2), t=M tau+y, v=d t, and u=gamma+c v.
All twelve supplied coordinates are positive. The roots identity gives
H8(v)=0, and the main norm gives (W-pv)^2=B. Thus R12=0.
This proves the existence equivalence.

## The product equation does not add extraneous signs

If Nk Nt(1+R12)=1, all three factors are integer units. Since hI is even,
R12 is a square modulo 4. Therefore 1+R12 cannot be -1 and R12=0.
Consequently Nk=Nt=epsilon for epsilon=+1 or -1. The authentic mask
bounds give C>=0 and the same weak outer bounds as in package 09:

    0<R<E-2, k=R+epsilon+hE>E, kY<c<k(Y+1).

The root reconstruction above is valid with precisely those weak bounds.
The existing signed Pell step-down then forces epsilon=+1. In particular
one must not assume C>0 before this sign argument. This is the same
boundary and sign-resolution obligation already discharged in 09's P13.

## Exact degrees

Every original unknown has weight one and every fixed port weight zero.
The relevant exact degrees are

    c=5, a=6, Delta=12, R=4, A=22, I=11,
    D=34, Q=d=46, P=92, Z=e=122, a0=214,
    M=23, N=114, B=22, W=p=11.

In the norm circuit, the unique highest term of vR is d^2 p^4 e^2,
of degree 380. The degree of vI is 201, uR is 190, and coef is 350.
Hence hR has unique top term d^4 p^8 e^4, of degree 760, while hI
has degree 581. The final norm has unique top term d^8 p^16 e^8,
of degree 1520. The product has degree 1520+7+2=1529.

Writing q0=beta J and k0=eta+zeta, the highest form of R12 is

    4^16 i^64 k0^144 w^112 s^256 q0^928(q0-F)^16.

It is nonzero for every beta>0. This proves an exact degree independently
of numerical specialization. The term of the product is this form times
[-h w s q0^4] times [w(q0-F-alpha)-z q0], also nonzero.

## A thirteen-variable intermediate construction

Retain f and use the ordinary strong equation I^2=K=Delta(f^2-1).
Put d=K-1, V=c(Tf-1)-Rf^2, e=KV^2-1. Set

    H4(v)=(v^2+d^2A-de)^2-4d^2 A v^2
    R13=Res_v(H4(v),(W-pv)^2-B).

The thirteen coordinates are the twelve above plus f. Use four equations

    Nk=1, Nt=1, I^2=K, R13=0.

The same main-root merger gives integer v, gamma=u-cv and rational t=v/d.
The identity H4(dt)=d^2[(dt^2+dA-e)^2-4d^2At^2] restores
tau=(dt^2+dA-e)/(2dt), then y=t-tau. Lemma 2 restores y's integrality.
There is no t=0 branch: it would imply (K-1)A=KV^2-1, hence
K|(A-1), whereas the outer bounds k>E, Y>=2 give

    0<A-1=k^2EY(EY+1)<k^4Y^4<c^4<=I^2=K.

The ordinary signed-gamma theorem proves soundness; canonical positive
witnesses give completeness with u=gamma+c d(tau+y).

The corresponding product is

    Nk Nt(1+I^2-K)(1+R13)-1.

The strong factor excludes -1 modulo 4 exactly as in package 09;
the new norm factor does so as above. The remaining outer signs are
resolved by the existing ordinary-rank argument.

For a division-free evaluator put

    r0=W^2+B, r1=2W
    sR=r0+p^2 d(dA-e)
    hR=sR^2+B r1^2-4d^2 A p^2 r0
    hI=r1(2sR-4d^2 A p^2)
    R13=hR^2-B hI^2.

Here hR has unique top form d^4 A^2 p^4 of degree 144; hI has
degree 83. Thus R13 has exact degree 288. The product degree is
288+22+7+2=319. This improves the previous explicit thirteen-variable
degree 515, although it has a longer evaluator. The four-equation
system has maximum degree 288 instead of 488.

Its nonzero highest form is

    (R13)_top=4^8 f^16 k0^16 w^32 s^48 q0^176.

For the product, multiply this by i^2 k0^4 s^4 q0^12,
by -h w s q0^4, and by w(q0-F-alpha)-z q0. The system evaluators
compare the last two norm terms directly, saving one subtraction versus
computing a zero residual. Their live-gate counts are 112 (twelve variables)
and 83 (thirteen variables). Product counts are 117 and 91, respectively.

## Reproduction

`build_mergers.py` emits division-free JSON circuits, exact gate ledgers,
upper degree propagation, and independent quadratic-pair/Horner evaluation
checks. Its optional symbolic checks concern the two monic identities and
the quadratic pair ring. The unbounded proofs above, not finite tests,
establish the Diophantine equivalences. The emitted packets deliberately
leave only the four fixed ports, to be bound by the parent report's whole
coefficient tuple; they do not themselves supply an alternative compiler.
