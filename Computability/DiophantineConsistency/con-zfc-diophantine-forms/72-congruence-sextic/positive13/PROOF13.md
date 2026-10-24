# Positive source coordinates and a fixed congruence inside a Pell root

## Result

This construction gives one fixed integer polynomial in thirteen strictly
positive unknowns, of exact total degree 28 and 98 live binary arithmetic
operations. Its predecessor in package 61 has degree 34 and 93 operations.
The new reduction is an ordinary mathematical proof; it does not constitute
a fresh end-to-end Lean or object-language ZFC proof. Its native compiler,
literal coefficient tuple, and Pell index interface are inherited, named
below. No assumption of consistency is made.

The new mechanism replaces the supplied native index J by the positive gap C.
All three quantities F, alpha, C become positive coordinates and their sum is
q. The fixed congruence on q is carried inside the normalized strong Pell
root. This removes the need for a degree-two positivity multiplier in the
transport carrier: transport positivity can be recovered at the end.

## 1. Exact integer polynomial

The thirteen positive inputs, in this order, are

    F, alpha, C, f0, i, T, X, Y, r, eta, zeta, u, gamma.

The four native fixed ports beta,K0,MC,MF are the WHOLE compact source44
tuple, beta=2^590069-1. MF is already shifted by beta. The following are
derived fixed integers, not independent parameters or witness variables:

    B=beta+1, b=3 beta, b2=b^2, L=beta b2, Kfinal=b2 L^2.

Define integer polynomial registers

    q=F+alpha+C, qm=q-1, q2=q^2, q3=q^3,
    k=eta+zeta, c=kY+eta, E=XY, ell=EkY,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    I=ic^2, Nf=b f0+q-B, F2=Nf^2,
    G=(q-1)(q-F)+alpha,
    Rhat=beta G(q^2-1)+(MC+q MF)(q-1),
    M0=q^3(q-1), Bt=(qK0+X)C-qF,
    Z=M0(ell+r)+(q-1)Y-q^3 Bt,
    Sb=4 beta qY, Mb=q Sb,
    Dhat=Mb(X+ac)+H[Mb gamma+Sb X-beta(k-1)+Rhat],
    Vhat=F2(beta cT-Rhat)-Lc,
    Yhat=Vhat+Lu.

The four residuals are

    A0=Z^2-M0^2[ell(ell+k)+1],
    A1=Dhat^2-Mb^2(1+Delta c^2),
    Aa=b2 Yhat^2-Delta(F2-b2)(Yhat^2-Vhat^2)-Kfinal,
    As=F2-b2(1+Delta I^2).

The actual integer polynomial is

    P13=A0^2+A1^2+Aa^2+As^2.

No rational coefficients, variable exponents, implicit divisions or hidden
quantified registers occur in this definition. `p13_degree28.json` is its
literal arithmetic DAG; `build13.py` regenerates it. Fixed expressions are
evaluated once from the four native integers, exactly as other fixed leaves
in the collection. The 98-operation count charges every live binary
addition, subtraction and multiplication on witnesses, including scalar
multiplication and squaring. Constant creation and register reuse are free.

## 2. Rational notation used only in the proof

It is convenient, before integrality has been recovered, to write

    f=Nf/b, J=(q-1)/beta, R=Rhat/beta,
    S=4qY, M=qS=4q^2Y, v=k-R-1,
    Dstar=M(X+ac)+H(M gamma+SX-v),
    V=f^2(cT-R)-c, U=Delta(f^2-1).

These are rational polynomial abbreviations, not new variables. Exactly,

    As=b2[f^2-Delta I^2-1],
    A1=beta^2[Dstar^2-M^2(1+Delta c^2)],
    Aa=b2 L^2[(V+u)^2-Uu(2V+u)-1].

The last identity uses Vhat=LV. All clearing factors are positive fixed
integers. Thus their zero sets agree with the simpler rational notation.

## 3. Inherited interfaces

Use the authentic normalized source interface stated in package61,
`positive/PROOF14.md`, section "Inherited interfaces", with the complete
compact tuple. A positive source tuple has q=beta J+1, X=wq, Y=sq^3,
C=q-F-alpha, the first Pell norm, main Pell norm, normalized strong norm,
the auxiliary Pell norm, index equation k-hE-R=1, and transport

    (K0+w)C+(q-F)-z_old(q-1)=1.

Its ordinary mathematical soundness yields a finite refutation in the fixed
ZFC calculus. Conversely, any such refutation has canonical positive source
witnesses with J=1 mod3, J>1, q=B^N, N odd,
X=2^R, R=3 mod4, c=psi_(a+2)(R), and
k=2 psi_(2XY^2+1)((R+1)/2). The canonical strong index can be chosen as
in that source. These are mathematical source theorems, not finite test
outcomes. The first positive gap needed below is proved directly in section8.

The signed auxiliary-index theorem is package61's
`positive/SIGNED_INDEX_LEMMA.md` and `positive/AUDIT12.md`: if
c=psi_A(p), f=chi_A(m), c divides m, m>2p, Maux^2=Delta(f^2-1),
c divides Maux, 0<p,R<c/2, and

    Maux^2 V^2-(Maux^2-1)y^2=1,
    V=-c mod f, V=-R mod c,

then p=R. V and y may have either sign. This is the precise named
inherited Pell theorem required below.

## 4. The fixed congruence is recovered first

At a positive zero, the four residuals vanish separately. Since q>=3 and
f0>=1,

    Nf=3 beta f0+q-beta-1 >= 2 beta+2 > 0.

The equation As=0 states that (Nf/b)^2=1+Delta I^2 is an integer.
A rational square root of an integer is an integer. Hence f=Nf/b is a
positive integer and b divides Nf. It follows that

    q-beta-1=3 beta j,  J=(q-1)/beta=3j+1

for an integer j. As q>0, j cannot be negative. Therefore J>=1,
q>=B>=16. Since beta=1 mod3, q=2 mod3. This reasoning did not assume
that J was integral or that the native index was already available.
R=Rhat/beta is now also an integer with exactly its source formula.

The supplied F,alpha,C are positive and q=F+alpha+C. Thus all source
packing bounds follow immediately, without using a transport sign:

    3q<R<q^4-2.

For completeness, G=q alpha+(q-1)C lies between q and q^2-q; the
authentic mask bounds give 0<(MC+qMF)J<(q-1)(1+2q). Hence
R<q^4-q^3+q^2-1<q^4-2, and its lower bound is stronger than 3q.

## 5. The transport carrier recovers divisibility without a sign demand

From A0=0, tau=Z/M0 is a rational square root of the integer
ell(ell+k)+1. Thus tau is an integer (possibly negative), and M0 divides Z.
Reduction modulo q^3 yields q^3|(q-1)Y, hence q^3|Y. Reduction modulo
q-1 yields q-1|Bt, since q^3 is coprime to q-1. Define proof-only integers

    s=Y/q^3>0, t=Bt/(q-1), tau=ell+r+s-t.

The first norm is tau^2-ell(ell+k)=1. Neither t nor tau is assumed
positive at this stage. Taking |tau| supplies the positive Pell root.
This is the step made possible by supplying C directly: source bounds
were already established and do not rely on t>0.

## 6. Recover the main root and both indices

After section4, Dstar is an integer; A1=0 implies that g=Dstar/M is an
integer square root of 1+Delta c^2. It is positive before any quotient
recovery. Indeed v=k-R-1<k, c>kY, H<5a, and MY>5, so

    Dstar > Mac-Hk > ak(MY-5)>0.

Thus g^2-Delta c^2=1. Since Y is a multiple of q^3 and q is coprime
to3, gcd(q,H)=1; H is odd and gcd(Y,H) divides3. Consequently

    gcd(S,H)<=3,  mu=S/gcd(S,H)>=4qY/3>q^4>R+1.

The carrier gives M|H(SX-v), and hence mu|v after reducing modulo S.
Both S and M divide 4XY^2: M divides it because Y/q^2 is integral.
This divisibility does not yet assume q|X.

Pell classification gives positive indices n,p with

    P0=2XY^2+1, A=a+2,
    |tau|=chi_P0(n), k=2 psi_P0(n),
    g=chi_A(p), c=psi_A(p).

Here P0>A and c>k, so n<p. The case n=1 is impossible: it would give
k=2, eta=zeta=1, c=2Y+1, whereas p>=2 and c>=2A>=4Y+4.
Thus n>=2 and

    c>kY>=4P0Y>8XY^3>=8q^9>2R,  c>2p.

The normalized strong equation from As=0 gives
f=chi_A(m), I=psi_A(m) for m>=1. Because I=ic^2, strong divisibility
implies p|m. Writing m=pv0, composition yields
I/c=psi_g(v0). Modulo c this is v0 g^(v0-1). Since g^2=1 mod c,
c divides v0. Hence c|m and m>=pc>2p.

Set Maux=Delta I. Its square is U=Delta(f^2-1), and c divides Maux.
The equation Aa=0 becomes

    Maux^2 V^2-(Maux^2-1)(V+u)^2=1.

Neither V nor V+u is zero. Moreover V=-c mod f and V=-R mod c;
the latter uses f^2=1 mod c, immediate from the strong equation.
All hypotheses of the stated signed auxiliary-index theorem now hold.
Therefore p=R. No transport sign, q|X, deleted h, or gamma_old was
used to obtain this conclusion.

The first Pell recurrence gives k=2n mod 4XY^2. Since mu divides S and
S divides 4XY^2, mu divides 2n-R-1. The strict bounds n<p=R<mu give
|2n-R-1|<R<mu. Thus 2n=R+1. Consequently

    v=k-R-1=k-2n

is a positive multiple of 4XY^2, and in particular of M. Returning to
M|H(SX-v), we obtain q|HX, hence q|X. Put w=X/q>0 and h=v/E>0.
These are integers. Also

    gamma_old=gamma+w-v/M

is an integer with g=X+ac+H gamma_old. Since n>=2, k>=4P0>X and
c>X; and g>(a+1)c. Thus H gamma_old>c-X>0, so gamma_old>0.

## 7. Recover transport positivity last

After q|X, Bt=q[(K0+w)C-F]. The divisibility q-1|Bt and
gcd(q,q-1)=1 imply that

    z_old = ((K0+w)C+q-F-1)/(q-1)

is an integer. Its numerator is strictly positive: K0,w,C>0 and
q-F=alpha+C>=2. Hence z_old is a strictly positive integer. This
argument permits the shifted quotient z_old-1 to be zero and does not
assert w>q for arbitrary source solutions. It is the exact place where
the old positivity multiplier is avoided.

The source transport holds. Taking T_old=fT and y=|V+u| restores every
positive normalized source coordinate. Its soundness yields a finite
syntactic ZFC refutation.

## 8. Constructive completeness

Start with canonical positive normalized source witnesses for a finite
refutation. Supply their F,alpha,C, so q=F+alpha+C. Set

    j=(J-1)/3, f0=f-j.

Then Nf=bf. The integer f0 is positive: f>=a+2>Y>=q^3>q>j. This uses
the normalized source Pell classification, not an assumed extra congruence
of f. As=0 follows exactly.

Keep X,Y,eta,zeta,i. Choose fresh positive T,u by the canonical
squared-modulus auxiliary reconstruction of package61: with
Maux=Delta I and canonical R=3 mod4,

    V*=chi_Maux(R)/Maux, y*=psi_Maux(R),
    T=(V*+c+Rf^2)/(cf^2)>0, u=y*-V*>0.

These quantities are integers, and give Aa=0. Their integrality is the
inherited odd-index polynomial congruence, not an assumption on arbitrary
old source coordinates.

Let t=q(z_old-1)>=0, since the source z_old is a positive integer. Define

    r=tau-ell-s+t, gamma=gamma_old+v/M-w.

The first is positive directly. Since n>=2, k>=4P0=8XY^2+4>3s, and

    tau^2-(ell+k/3)^2=k^2(XY^2/3-1/9)+1>0.

Thus tau-ell>k/3>s.
The second is positive because v is a positive multiple of 4XY^2, so
v/M>=XY/q^2=wY/q>=wq^2>w. Substitution gives Z=M0 tau and
Dstar=Mg. Thus A0=A1=0. Every supplied witness is positive.

Both existence implications are therefore established. Composing with the
identified source calibration and negating proves, by ordinary arithmetic
formalizable in ZFC,

    P13 has no strictly positive integer zero  iff  Con(ZFC).

This equivalence does not settle either side. Full formal certification of
this particular literal circuit and the native semantic bridge remains
distinct from the repository's existing closed consistency equations.

## 9. Exact degree and reproducible audit

Each supplied witness has degree1 and every fixed port has degree0.
Rhat has degree4, c degree2, a degree2, Delta degree4, ell degree4,
Nf degree1, and I degree5. The cancellations

    Z=M0 ell+Ztail,
    A0=2M0 ell Ztail+Ztail^2-M0^2(ell k+1),
    Dstar=M(ac+X+H gamma)+H(SX-v),
    (X+ac+H gamma)^2-(1+Delta c^2)
      =2ac(X+H gamma)+(X+H gamma)^2-Hc^2-1,
    Yhat^2-Vhat^2=Lu(2Vhat+Lu)

show that A0,A1,Aa have degree at most13. Each is exactly13; e.g.
their respectively nonzero leading terms contain r, gamma, and u.
The strong residual As has degree14 and leading homogeneous part

    -9 beta^2 i^2(eta+zeta)^4 X^2Y^6.

It is the only residual with this degree. Therefore P13 has exact degree28,
with leading form

    81 beta^4 i^4(eta+zeta)^8 X^4Y^12.

The coefficient of i^4 eta^8 X^4Y^12 is 81 beta^4>0 for the actual
native numeral, independently of K0,MC,MF. No specialization cancellation
can invalidate the exact degree.

The literal circuit has98 live operations:25 additions,16 subtractions,
57 multiplications. Its four-residual system costs91 operations. These
are arithmetic-circuit counts, not bit complexity or expanded coefficient
size. The source has four independent native integer ports and six derived
fixed leaves; each derived leaf is specified by its exact arithmetic recipe.

`check13.py` independently reads the circuit as data, checks exact symbolic
residual identities and degrees, verifies the sum-of-squares suffix over
independent residual symbols, and checks liveness/counts. Finite synthetic
examples of carrier recovery supplement the universal proof but cannot
test consistency or establish unbounded source semantics.
