## Final evaluator update

The delivered evaluators use 93 gates for P13, 104 for the P12 product,
and 103 for the P12 sum of squares. The following review also discusses
the preceding 95/105/104-gate evaluators. Exact symbolic checks prove
equality of their polynomials; the original packets are retained in
reference/. See CIRCUIT_OPTIMIZATION.md for the three local identities.

# Independent audit of the 12-positive degree-118 construction

Reviewed files: `root_opt/build12.py` and `root_opt/p12_product_split2.json`.
Reviewed circuit SHA256:
`54347f9c2225230df7a23946c199126e36683a69da09c5e10f5f25234d0a3248`.

**Finding:** no error found in the new elimination, domain handling, canonical
congruence, or literal circuit. The equation has twelve positive variables,
exact degree 118, and 105 live binary gates (61 multiplications, 26 additions,
18 subtractions). Its three residuals have exact degrees 15,17,86. This is an
internal independent AI-assisted review, not external peer review or a
proof-assistant certificate.

## Executed exact checks

The independent `root_opt/check12.py` reads the emitted graph as data and does
not import its builder. It uses only the Python standard library.

- Every register in the prefix used for A0,A1,D,Caux,Maux,Q,V is expanded as an
  exact sparse polynomial in all twelve witnesses and four symbolic ports,
  and compared with separately specified formulas. The first carrier is
  specified in its older unfactored form to check the factoring identity.
- The norm suffix is checked exactly over independent registers D,M,C,V,n;
  the product finalizer is checked exactly over independent A0,A1,N. These
  cut identities compose with the exact prefix, so no random test replaces
  a literal polynomial identity.
- Exact sparse leading forms check the canceled carrier degrees, the two
  degree-43 summands in normA, and the nonzero degree-118 output form.
- All gates and all declared inputs are live; operation count is exactly105.
- The all-value recovery identities below are checked in an independent small
  polynomial ring. Sixty-four finite Pell residue examples supplement the
  all-index recurrence proof below, without replacing it.

The checker passes both normally and under `python3 -O` and writes
`root_opt/CHECK12.json`. Full expansion of the final enormous polynomial is
unnecessary; the cut identities and leading forms are exact.

## Elimination and exceptional branches

Use the builder's balanced factors

    I=i c^2,
    D=1+Delta I^2,
    M=Delta i c^3, Caux=Delta i c,
    Q=M Caux=(Delta I)^2, d=Q-1,
    V=D(cT-R)-c.

For positive inputs, c>=3, Delta>0, M>1, D>c+1 and Q>1. In particular

    B=2d(Mn-1)>0.

There is no zero-denominator branch. Set

    A=dM(n^2+D)-2dn+Caux(1-V^2),
    N=A^2-B^2D.

At N=0, f=A/B is rational with f^2=D an integer. Rational-square-root
integrality therefore gives f an integer; f!=0 because D>1. Let t=n-f.
The exact identities are

    A-Bf=dM t^2-2dt+Caux(1-V^2),
    M(A-Bf)=d(Mt-1)^2-QV^2+1,   when f^2=D.

Thus y=Mt-1 is an integer and QV^2-(Q-1)y^2=1. Neither its sign nor the sign
of f needs an extra hypothesis. Replace f by |f| and y by |y|; every other
occurrence of f depends only on f^2=D, and the auxiliary equation uses y^2.
The value y cannot be zero because QV^2=1 has no integer solution when Q>1.

A useful direct bridge to P13 avoids even a signed-root formulation:
V=D b-c with b=cT-R an integer, D>c+1 and c>=3. If b<=0 then V<=-c<-1;
if b>=1 then V>=D-c>1. Hence |V|>1 for every positive input, even before
assuming any equation. The auxiliary norm gives

    (Q-1)(y^2-V^2)=V^2-1>0,

so |y|>|V|. Therefore u=|y|-V>0. Set the old P13 coordinate j13=2j12,
f13=|f|, and u13=|y|-V. Since J13=3j13+1=6j12+1, its outer registers are
identical; normalized strong and auxiliary residuals both vanish. This is
an explicit positive lift of every P12 solution to the proved P13 kernel.

## Product finalizer

J=6j+1 and beta=2^590069-1 are odd, so q=beta J+1 is even. Therefore
M0=q^3(q-1) and U=q^5 are even. The first two residuals are squares modulo4:

    A0=Z^2-M0^2*(...), A1=Dstar^2-U^2*(...).

The third residual N is also a square modulo4 because B is even. At a zero
of (1+A0)(1+A1)(1+N)-1, the three integer factors are units. A factor -1
would make its residual -2=2 mod4, impossible for a square modulo4. All
three factors are +1, hence A0=A1=N=0. Conversely those three equalities
clearly zero the product. Positivity of the residuals themselves is neither
assumed nor required.

## Canonical y=-1 moduloQ

For every integer x, write v_r(x)=psi_x(2r+1). Its integer recurrence is

    v_0=1, v_1=4x^2-1,
    v_(r+1)=(4x^2-2)v_r-v_(r-1).

Modulo x^2 this has initial values1,-1 and recurrence
v_(r+1)=-2v_r-v_(r-1); induction gives v_r=(-1)^r modx^2.
Take x=Delta I and canonical R=2r+1=3 mod4. Then r is odd and

    y_old=psi_(Delta I)(R)=-1 mod(Delta I)^2=-1 modQ.

Since M dividesQ, t=(y_old+1)/M is a positive integer. The new witness
n=f_old+t is positive and gives A=Bf_old, hence N=0. This proves canonical
completeness of the elimination. It does not impose the congruence on every
arbitrary old auxiliary witness. The required canonical witness can be
reselected using the already established odd-index construction.

The restriction J=6j+1 is also legitimate canonically: B_native is even,
so its repunit J is odd, and its odd exponent gives J=1 mod3. Thus J=1 mod6;
padding ensures J>1, so the new j is positive.

## The signed auxiliary-index theorem has no missing sign premise

For an independent review of the P13 proof boundary, the relevant elementary
lemma can be proved as follows. Suppose A>=2, Delta=A^2-1,
c=psi_A(p), f=chi_A(m)>0, c|m, m>2p, Maux>1, c|Maux,
Maux^2=Delta(f^2-1), 0<p,R<c/2, and integer V,y satisfy

    Maux^2 V^2-(Maux^2-1)y^2=1,
    V=-c modf, V=-R modc.

Classify the positive Pell solution (Maux|V|,|y|), obtaining an index
ell>=1. Its abscissa is divisible by Maux, so ell is odd, ell=2u+1.
Write chi_x(ell)=x Q_u(x^2). The recurrence gives

    Q_u(0)=(-1)^u ell,
    Q_u(1-A^2)=(-1)^u psi_A(ell).

The possible sign V=+/-Q_u(Maux^2) disappears upon squaring the congruence
modf. Since Maux^2=1-A^2 modf, it yields

    chi_A(2ell)=chi_A(2p) modf.

Here the plus-congruence step-down can be seen directly, without an extra
positivity premise on V. In the Pell ring modulo f=chi_A(m), the fundamental
unit to power2m is -1, because psi_A(2m)=2chi_A(m)psi_A(m)=0 modf and
chi_A(2m)=2f^2-1=-1 modf. Reducing ell modulo m and reflecting if necessary
reduces chi_A(2ell) to a signed chi_A(2s), 0<=s<=m/2. If 2s=m it is zero
modf, impossible since 0<chi_A(2p)<f. Otherwise both chi_A(2s) and
chi_A(2p) are at most chi_A(m-1), and

    2chi_A(m-1)<chi_A(m)=f.

Hence neither a nonzero difference nor a positive sum can be divisible byf;
the congruence forces s=p. Thus ell=+p or -p modm, hence modulo c.
Modulo c the first quotient identity also gives ell=+R or -R modc.
The strict bounds 0<p,R<c/2 force p=R. This proof allows both signs of V,y.

All inputs to this lemma are explicitly obtained in PROOF13.md before its
use: first-root recovery gives q^3|Y; the transport carrier gives C>0 and
R<q^4; the n_first=1 exclusion gives c>8q^9>2R; normalized strong divisibility
gives c|m and m>2p. Thus neither deleted quotient nor the later q|X conclusion
is used circularly. A negative f from the new norm is harmless because its
absolute value has the same square and every needed congruence is modulo
that positive absolute value.

## Exact degree certificate

Let q0=6beta j, k0=eta+zeta,
R0=q0^3(q0-F), B0=(K0q0+X)(q0-F-alpha)-q0F. The exact leading form is

    -16 q0^18 i^10 k0^21 X^15 Y^35 gamma B0
        *[k0^2 X^2 Y^4-R0^2]^2.

Its coefficient at

    j^18 i^10 eta^25 X^20 Y^43 gamma alpha

is exactly 16(6beta)^18>0. This is independent of K0,MC,MF, so specialization
to their fixed huge values cannot cancel the top degree. This establishes
exact degree118, not merely a propagated upper bound.

## Remaining limitations

The audit certifies the literal algebra and reviews the new unbounded
mathematical reduction. It does not independently regenerate coefficient
bytes, reprove the inherited native-window compiler or K215/refutation
calibration, establish global minimality, supply a proof-assistant
certificate, or decide whether the equation has a zero. The positive domain
must be stated; it is not a twelve-unrestricted-integer claim.
