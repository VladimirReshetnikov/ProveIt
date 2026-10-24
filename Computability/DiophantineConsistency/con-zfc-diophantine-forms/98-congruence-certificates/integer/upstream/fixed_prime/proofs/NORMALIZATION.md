# Independent normalization and canonical-completeness audit

This note verifies the normalization adapter proposed during the current
iteration. It is an ordinary unbounded mathematical proof, with small exact
diagnostics in `code/check_adapters.py`; it is not a proof-assistant certificate.

## 1. Source notation

For an integer A >= 2 put Delta=A^2-1, and define

    chi_A(n)+psi_A(n) sqrt(Delta)=(A+sqrt(Delta))^n.

Thus chi_A and psi_A have recurrence u(n+2)=2A u(n+1)-u(n).
We use their Pell identity, composition identity and integer coefficients.
The canonical source has

    A=a+2, R>=3, R=3 mod4, c=psi_A(R),
    a=(X+1)Y, X=2^R, Y=(2v+1)q^3, q a positive power of2.

Consequently a is even, A is even, c is positive odd, and Delta is positive
odd. This applies to the source34 canonical family used by the incoming
Pell-congruences packet; no compact44/source34 port mixing is needed.

The even-a restriction costs no coordinate. Replace the source's J=3j+1
by J=6j+1. Since beta is odd, q=beta J+1 is then even identically;
Y=(2v+1)q^3 and a=(X+1)Y are even identically. Canonical source34 J is
1 modulo6: it is the odd-length repunit 1+B+...+B^(N-1), with B even,
B=-1 modulo3, and N odd. Thus this stronger affine restriction loses no
canonical existence witness. Its q=2 modulo3 orientation is unchanged.

## 2. An explicit odd normalized strong witness always exists

**Lemma.** If A>=2 is even and R>=3 is odd, set

    c=psi_A(R), D=chi_A(R), m=R c,
    I_new=psi_A(m), f=chi_A(m).

Then I_new/c^2 is a positive odd integer. In particular there exists r in Z
such that

    i=2r+1, I_new=i c^2, f^2-Delta I_new^2=1.

**Proof.** Reducing the psi recurrence modulo2 gives psi_A(n)=n mod2.
Thus c and m are odd, and I_new is odd. Composition gives

    I_new=c psi_D(c).

The main Pell identity gives D^2=1 modc. Induction in the recurrence yields

    psi_D(t)=t D^(t-1) modc  (t>=1).

Indeed the induction step replaces 2D*t D^(t-1)-(t-1)D^(t-2) by
(t+1)D^t using D^2=1 modc. At t=c the expression is zero modulo c.
Therefore c^2 divides I_new. Since both I_new and c^2 are odd, their
positive quotient i is odd. The normalized strong identity is the Pell
identity at m. This proves the lemma.

This is a constructive choice, not an appeal to cofinality of a set of
Pell witnesses. No previous strong witness needs to be preserved.

## 3. Restore the ordinary odd strong coordinate

Define

    I_old=Delta I_new, i_old=Delta i,
    r_old=(Delta(2r+1)-1)/2.

Because Delta and i are odd, r_old is an integer and i_old=2r_old+1.
Moreover

    I_old^2=Delta^2 I_new^2=Delta(f^2-1),
    I_old=(2r_old+1)c^2.

These are exactly the ordinary odd-strong equations used by the integer
source. The quotient f is reconstructed from the square condition

    f^2=D_f:=1+Delta(2r+1)^2 c^4.

The rewritten auxiliary coefficient is

    Q=I_old^2=Delta^2(2r+1)^2 c^4.

The transformation is integral on the stated even-a slice. In a soundness
argument Delta need only be odd for the parity restoration; its positivity
and the remaining source inequalities may instead be recovered by the
source's established sign and rank argument.

## 4. Explicit squared-modulus auxiliary reconstruction

Assume R=3 mod4, c=psi_A(R), and f,I_new are positive integers satisfying

    f^2-Delta I_new^2=1, c divides I_new.

Put M=Delta I_new and R=2s+1, so s is odd. There is an integer polynomial
Q_s(z) such that chi_Z(2s+1)=Z Q_s(Z^2). Its standard evaluations are

    Q_s(1-A^2)=(-1)^s psi_A(2s+1),
    Q_s(0)=(-1)^s(2s+1).

Choose

    V*=chi_M(R)/M=Q_s(M^2), y*=psi_M(R).

Both are positive integers and

    M^2(V*)^2-(M^2-1)(y*)^2=1.

Since M^2=Delta(f^2-1)=1-A^2 mod f^2 and c divides M, the two
polynomial evaluations imply

    V*=-c mod f^2, V*=-R modc.

Also f^2=1 modc and gcd(c,f^2)=1. Hence

    T=(V*+c+R f^2)/(c f^2)

is an integer: its numerator is divisible by f^2 and by c, and these
moduli are coprime. It is positive. Thus

    V*=f^2(cT-R)-c.

With T_old=fT, this is also

    V*=fcT_old-f^2R-c,

the old CRT expression. No assertion that an arbitrary old T_old is
divisible by f is needed; completeness selects this explicit witness.

The same argument is fully set out in source61's
`positive/SIGNED_INDEX_LEMMA.md`, section5. It is independent of the
compiler tuple and therefore transfers to the source34 family.

## 5. Rational auxiliary roots really are integral

The merged radical may initially recover only rational y. The needed
coefficient-independent lemma is:

    Q>1 integer, V integer, y rational,
    Q V^2-(Q-1)y^2=1  ==>  y integer.

Here is the complete descent. Change signs to make V,y positive. Write
y=b/d in lowest terms, d>0. Then d^2 divides Q-1, so d divides Q-1.
If V=1 then y=1. For V>1 define

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The first is an integer, the same norm identity holds, and the reduced
denominator of y' is d because 2Q-1=1 mod d. Moreover y>V and
QV>(Q-1)y, whence -V<V'<V. The norm excludes V'=0. Strong induction on
|V| reaches V=1 while preserving d, and gives d=1.

In the normalized candidate Q=Delta^2 i^2 c^4. The restored source's
preliminary bounds have c nonzero and |c|>2; Delta is nonzero because
A is even, while i is odd nonzero. Hence Q>1 before applying descent.
The case Q=1 cannot be silently passed through a denominator clearing.

For the five-radical construction, denominator clearing is safe even
earlier: Delta=0 modulo3 implies Q=0 modulo3, so Q-1 is nonzero without
any positivity assumptions. First recover all rational roots by the
3-adic separation lemma; then the fifth square condition gives the
positive guard; then derive |c|>2 and Q>1; only then use the descent to
prove the auxiliary rational root integral. This ordering avoids a
circular dependence on the merged positivity guard.

## 6. Residues needed by fixed 3-adic weights

The affine source restrictions give X=2 mod3, hence a=(X+1)Y=0 mod3.
Therefore Delta=(a+2)^2-1=0 mod3 and H=4a+3=0 mod3. All four
relevant squared roots are 3-adic units:

* first Pell: 1+b(b+1)k^2=1 mod3, because b=XY^2 is 0 or2 mod3;
* normalized strong: D_f=1+Delta i^2c^4=1 mod3;
* main: 1+Delta c^2=1 mod3;
* auxiliary: (QV^2-1)/(Q-1)=1 mod3, because Q=0 mod3.

H=4a+3 is a nonzero odd integer. Thus weighting the first, strong and
auxiliary radicals by 3H,9H,27H and the main radical by1 makes the
3-adic valuations of their coefficients respectively v3(H)+1,
v3(H)+2,v3(H)+3,0, all distinct. Reconstruction of the main-root
congruence is compatible with this choice, since the other coefficients
are all multiples of H.

## 7. Source references and scope

* ProveIt at cfbf118b4ad9b2c651fe96b571d9415261766328:
  `61-congruence-carriers/positive/SIGNED_INDEX_LEMMA.md` (especially5),
  `69-cones-pell/positive/PROOF.md` (rational-integrality descent),
  `70-residue-orientation/integer/PROOF.md` (source34 canonical parity),
  and incoming Pell-congruences `transport/PROOF.md` (CRT expression).
* The present note verifies the adapter and canonical availability; the
  complete new polynomial, norm construction, degree and endpoint binding
  are the responsibility of the main construction and its audit.
