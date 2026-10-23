# Ordinary-strong radical merger: twelve positive unknowns, degree 316

## Result, interpretation, and inherited boundary

The single equation below has twelve strictly positive supplied integer unknowns,
exact total degree 316, and 102 binary arithmetic operations (61 multiplications
and 41 additions/subtractions). Its three-equation system has residual degrees
2,26,288 in 95 operations, or 94 after the positive transport-coordinate shift.
All scalar multiplications are charged; fixed numeral leaves, register reuse,
and system comparisons are free. Every supplied variable, port, and gate is live.

This strictly improves the authenticated source52 twelve-positive frontier
(degree 897 in 108 operations), on degree and operations. It does not improve
its eleven-positive variable count, prove global optimality, or give a new
end-to-end proof-assistant verification. The statement is an ordinary mathematical
reduction formalizable in ZFC: the displayed equation has no positive solution
if and only if Con(ZFC). It is not a proof of either side of this equivalence.

The four fixed coefficients are exactly one complete authentic normalized
blank-K215 tuple. The delivered instance is the materialized source31 Wang943
121-by-8801 tuple, beta=2^1064921-1, with MF already the shifted MF_source.
All payloads and both compressed/raw hashes are supplied. The complete tuple
adapter is preserved as upstream/COEFFICIENT_PROOF.md. The ordinary signed
compiler theorem, Pell rank and saturation arguments, and its normalized-to-
ordinary bridge are preserved in upstream/ORDINARY_BLANK_PROOF.md. Source50's
quotient absorber and early-index bootstrap are preserved in
upstream/FOURTEEN_ABSORPTION_PROOF.md. The unbounded native compiler and literal
K215/refutation calibration remain inherited theorems, not facts certified
by finite arithmetic checks. Arbitrary illustrative port values do not define
the calibrated consistency equation.

The new idea is to retain f but eliminate the ordinary strong coordinate i,
together with tau and y. This uses Q=Delta(f^2-1), of degree 14, instead of
Q=Delta^2(ic^2)^2, of degree 46. A weighted three-root sum forces rationality;
ordinary Pell saturation then restores integrality of both y and sqrt(Q)/c^2.
A denominator-deflated two-radical norm supplies the low degree.

## 1. Explicit polynomial and division-free evaluator

The twelve strictly positive supplied variables are

    J,F,alpha,z,f0,T,s,w,eta,zeta,gamma,t.

All following names are computed polynomial abbreviations, not variables:

    q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)Cw+q-F-z(q-1),
    U=4q^4, u=k-R-1, Dstar=U b0+H(U gamma-u),
    Nmain=Dstar^2-U^2 G,
    f=f0+1, Q=Delta(f^2-1), d=Q-1,
    V=c(Tf-1)-Rf^2, Eaux=QV^2-1, M2=2f ell,
    Z=c^4 M2^2 Eaux, x=c^2 t, r=c^4 f^2 A,
    M=d(x^2+Q+r)-Z,
    C0=M^2+4d^2[x^2(r-Q)-Qr], B=2dQ-M,
    Ninner=C0^2-16d^2 x^2 r B^2.

The recommended single equation is

    P=Nt(1+Nmain)(1+Ninner)-1=0.                  (1)

The system is Nt=1, Nmain=0, Ninner=0. The alternative sum of squares is
(Nt-1)^2+Nmain^2+Ninner^2=0, of degree 576 in 103 operations. Exact inert
JSON gate lists give all definitions without division or implicit parameters.

The inner polynomial is the four-factor formal product

    Ninner = product over rho^2=Q, tau^2=A of
       [ d(c^2 t-rho-c^2 f tau)^2-c^4 M2^2 Eaux ]. (2)

Both formal signs of each root occur. To verify the evaluator, replace
c^2 f tau by a formal root b with b^2=r. Each factor is
M-2dx rho-2dx b+2d rho b. First taking its norm in rho gives

    C0+4dx(2dQ-M)b.

Taking the norm in b gives the displayed Ninner. This is a polynomial-ring
identity, including zero, square, coincident, and negative specializations.
Formal signs are not asserted to be independent Galois automorphisms.

Equivalently, let zeta0^2=d Eaux. The eight-factor linear norm of

    c^2 d t-d rho-c^2 d f tau-c^2 M2 zeta0

is exactly d^4 Ninner: eliminate the two zeta0 signs first. Removing this
common d^4 explains the degree reduction. No division is performed by the
actual circuit, and d>0 will be verified before using the zero-set equivalence.

## 2. Unit guard and initial bounds

Ninner=C0^2 modulo 16. Since U=4q^4, also Nmain=Dstar^2 modulo 16.
At a zero of (1), all three integer factors Nt,1+Nmain,1+Ninner are units.
Neither Nmain nor Ninner can equal -2, since -2 is not a square modulo 4.
Thus Nmain=Ninner=0 and Nt=1. Conversely these three equalities imply (1).

The authentic weak transport interface, exactly as in the preserved ordinary
proof, now supplies

    q>=16, Cw>0, q-F>0, 3q<R<q^4-2,
    X>=q, Y>=q^3, E>=q^4>R+2,
    k>=2, kY<c<k(Y+1), a+2<2E.

For clarity, Cw>0 follows already from Nt=1: if Cw<=0 then
Nt <= q-F-z(q-1)=1-F-(z-1)(q-1)<=0. The R bound is the inherited mask
bound for the whole selected tuple, not an arbitrary-port assumption.
Because f=f0+1>=2, Q=Delta(f^2-1)>1 and d>0. No Q=0, d=0, or f=1
case is silently discarded; the explicit positive shift excludes them.

## 3. The main root and absorbed congruence

Nmain=0 gives the rational square root g=Dstar/U of the integer G. Hence
g is integral. It is positive. Indeed H<5a and b0>akY, while gamma>0,
u=k-R-1<k, and UY>5 give

    Dstar>U b0-Hk>ak(UY-5)>0.

Thus g^2-Delta c^2=1. Reducing Dstar=Ug modulo U gives

    U divides H(k-R-1).                          (3)

There is no premature cancellation of H, and neither gamma_old nor h has
been recovered at this point.

## 4. Weighted square-class separation recovers all inner roots

Put rho=sqrt(Q)>0 and tau=sqrt(A)>0. If V=0, then Eaux=-1 and every
factor in (2), evaluated with real rho,tau, is strictly positive:
its value is d(real number)^2+c^4 M2^2. This contradicts Ninner=0.
Therefore V is a nonzero integer. Consequently Eaux>=Q-1=d and the positive
real number y=sqrt(Eaux/d) satisfies y>=1.

A zero factor in (2) gives signs epsilon_j in {+1,-1} with

    t=epsilon_1 rho/c^2+epsilon_2 f tau+epsilon_3 M2 y. (4)

These are three rational multiples of square roots of positive integers:
y=sqrt(d Eaux)/d. The following strict bounds hold before any rationality
claim. Since rho<(a+2)f, tau<ell+k, and

    ell-k=k(EY-1)>=2EY-2>2E>a+2,

we have

    0<rho/c^2<f ell<f tau,
    rho/c^2+f tau<f(a+2+ell+k)<2f ell=M2<=M2 y. (5)

Distinct squarefree radicals are linearly independent over Q. In a rational
signed sum, the signed coefficients in every irrational square class must
therefore sum to zero. The largest term M2 y exceeds the sum of both other
terms by (5), so its square class cannot cancel unless y is rational.
Once y is rational, the middle term f tau strictly exceeds rho/c^2; thus
the remaining two terms cannot cancel in an irrational square class either.
It follows that y,tau,rho are rational. This argument does not assume that
Q,A,d Eaux have independent square classes; it explicitly allows coincidences.
Rational square roots of integers are integers, so rho and tau are integral.

The rational y satisfies

    rho^2 V^2-(rho^2-1)y^2=1.                    (6)

Here rho>=2 and V is integral. Rational Pell saturation makes y integral.
A proof is given in Section 5. Equation (4) then makes rho/c^2 integral,
because t, f tau, M2 y are integers and all signs are units. Define

    i=rho/c^2>0.

We have recovered precisely the ordinary strong equation

    (ic^2)^2=Delta(f^2-1),

along with tau^2=1+ell(ell+k) and QV^2-(Q-1)y^2=1. Replacing the recovered
roots by their positive values is harmless for all three equations. No
unproved cancellation of Delta and no rank theorem has been used yet.

## 5. Rational Pell saturation

If m>=2 and V are integers and rational y satisfies
m^2V^2-(m^2-1)y^2=1, write y=b/r in lowest terms, r>0. Then r^2|m^2-1.
For D0=(m^2-1)/r^2, the pairs (m,r) and (m|V|,|b|) are nontrivial
integer-coordinate Pell solutions. D0 is positive and nonsquare: m^2-1
is not an integer square, and division by an integer square cannot change
its square class. Write their indices in the fundamental integer-coordinate
Pell group as j,l. The abscissa at j divides the abscissa at l.
The identities chi_(n+2j)=-chi_n and chi_(2j-n)=-chi_n modulo chi_j
reduce and reflect l into [0,j]. Strict growth excludes every representative
less than j, so l is an odd multiple of j. The ordinate addition formulas
then show r divides |b|. Reducedness forces r=1. V=0 or y=0 is impossible
in the original equation. This proves the lemma used in Section 4.

## 6. Early index bound, ordinary rank, and compiler restoration

This section applies the preserved source50 argument to the roots just
recovered. Details are included to make the dependency order explicit.
Let A0=a+2 and P0=2EY+1. The main and first Pell equations have indices
p,n>=1 with

    g=chi_A0(p), c=psi_A0(p),
    tau=chi_P0(n), k=2psi_P0(n).

The first equation's fundamental integer-coordinate unit is (2EY+1,2)
for discriminant EY(EY+1); ordinate 1 lies strictly between consecutive
squares, while ordinate 2 is attained. P0>A0 and c>k imply p>n.

The recurrence modulo P0-1 gives k=2n modulo 4EY. Since
4EY=4w s^2 q^7 is divisible by U=4q^4, (3) gives
2n=R+1 modulo mu=U/gcd(U,H). H is odd, and H=3 modulo q. A prime common
to q and H must be 3; if 3|q then H=3 modulo 27, so its 3-adic valuation
is exactly one. Therefore gcd(U,H)<=3 and

    mu>=4q^4/3>R+1.

Since n>0, the congruence forces 2n=R+1+j mu with j>=0, hence
n>=(R+1)/2. Thus n>=25 and p>=26. Pell growth now proves, before invoking
ordinary strong rank,

    c>A0 Delta^2, c>2p, c>2R.

For the first bound use c>=A0^25>A0^5>A0 Delta^2; for the last,
c>=psi_A0(2)=2A0>2R.

The ordinary strong-rank theorem (preserved ordinary proof, Section 4)
applied to c=psi_A0(p)>A0 Delta^2 and (ic^2)^2=Delta(f^2-1) supplies

    f=chi_A0(m), p|m, c|m, m>=c>2p,
    ic^2=Delta psi_A0(m), c^2|(f^2-1).           (7)

This is not an informal inference by dividing the strong equation by Delta.
Its proof handles a possibly nonfundamental parameter in the underlying
squarefree Pell field, first using gcd-index growth to obtain p|m, then
composition and gcd(c,Delta)=gcd(p,Delta) to obtain c|m.

The auxiliary equation (6), the polynomial identity for odd Pell abscissas,
and V=-c modulo f give an odd auxiliary index j0 with j0=+/-p modulo m.
The congruences Q=0 modulo c and V=-R modulo c, using (7), give
j0=+/-R modulo c. Since c|m and 0<p,R<c/2, these imply p=R. The signed
abscissa reduction uses 0<2p<m and 2chi_A0(m-1)<chi_A0(m), so a negative
reduced representative cannot mimic chi_A0(2p). This is the preserved
ordinary proof's signed auxiliary argument, not a positivity assumption on V.

Now 1<=n<R, so |2n-R-1|<R<mu. Thus j=0 and 2n=R+1.
The same recurrence modulo 4EY gives u=k-2n divisible by 4EY, hence both
E and U. Set

    h=u/E, gamma_old=gamma-u/U.

The first is positive because psi_P0(n)>n for n>=25. The carrier gives
gamma_old=(g-b0)/H. Since n>=2, k>=4P0>X and c>X. Also g>(a+1)c,
so g-b0>c-X>0 and gamma_old is positive.

All positive ordinary compiler coordinates are now restored, with Nt=1,
k-hE-R=1, the two original Pell norms, the ordinary strong equation, and
the auxiliary equation. The inherited ordinary signed compiler theorem
extracts a blank K215 halt and hence a finite ZFC refutation.

## 7. Constructive completeness

Start with a canonical positive ordinary compiler witness. Its established
index theorem gives p=R=2n-1, so u=k-2n is a positive multiple of 4EY and
therefore of U. Define

    gamma=gamma_old+u/U,
    f0=f-1,
    t=i+f tau+M2 y.

All are strictly positive integers: the strong equation forces f>=2.
Keep the other nine retained coordinates. Then Dstar=Ug, so Nmain=0.
Since rho=ic^2, the positive-sign factor in (2) becomes
c^4 M2^2[d y^2-Eaux]=0, so Ninner=0. Nt=1 is unchanged. Thus (1) has
a positive solution. Canonical normalized witnesses provide ordinary ones
via the preserved substitution i_ordinary=Delta i_normalized if needed.

For the shifted system use (K0+w)Cw=F+z(q-1) instead of Nt=1. This is
z_old=z+1. Soundness follows by substitution. Canonical witnesses have
X=2^R, Cw>0, w=2^R/q>q>F, which force z_old>=2; thus the shifted z is
positive. It saves one gate without changing any degrees.

Combining both directions and the inherited literal K215/refutation
calibration gives the claimed Con(ZFC) equivalence by negating existence.

## 8. Exact degrees and nonzero leading forms

Every supplied variable has degree one; the four fixed coefficients degree
zero. Let

    q0=beta J, Y0=sq0^3, E0=wq0Y0, k0=eta+zeta, c0=k0Y0.

Their degrees are 1,4,6,1,5. The shifted f has highest form f0.
The leading quantities in the new inner norm are

    Q0=E0^2 f0^2                         (degree 14),
    V0=c0 T f0                           (degree 7),
    (M2)0=2f0 E0 c0                      (degree 12),
    Z0=4E0^4 c0^8 T^2 f0^6              (degree 72).

All other terms in M=d(x^2+Q+r)-Z have degree at most 58. Therefore
M_top=-Z0, C0_top=Z0^2, and the subtracted term in Ninner has degree
at most 238, below 288. Thus

    (Ninner)_288=Z0^4=2^8 E0^16 c0^32 T^8 f0^24, (8)

nonzero for every beta>0. This is an exact fixed-instance degree proof.

For the main residual write

    Nmain=U^2[(b0+H gamma)^2-G]
           -2UH u(b0+H gamma)+H^2u^2.

The bracket has exact degree18, with highest form 8E0^2 c0 gamma;
the other two displayed terms have degree at most25 and20. Since
U0=4q0^4, the exact degree26 leader is

    (Nmain)_26=128q0^8 E0^2 c0 gamma.             (9)

The transport degree2 leader is
Nt_2=w(q0-F-alpha)-zq0, nonzero for every beta>0. Hence

    P_316=2^15 q0^8 E0^18 c0^33 gamma T^8 f0^24 Nt_2.

This proves exact degree316 without generic-port assumptions. The system
residual degrees are 2,26,288, and the sum of squares has exact degree576.
No delicate formal-radical leading cancellations are needed for the inner norm.

## 9. Reproduction and diagnostic scope

Run build_ordinary_merger.py, check_ordinary_merger.py, and the checker again
under python -O. The checks verify all fixed payload hashes; 36 signed exact
integer four-factor products and denominator-deflation identities; 100 modular
versions; both mod16 guards; 144 pre-index bound stresses including X much
larger than k; 24 complete finite-field polynomial rays across all presentations,
including the actual coefficient tuple; exact analytic leaders; and 24 transport
coordinate shifts. The independent products treat JSON as inert arithmetic
records and do not execute received upstream programs.

These finite checks corroborate algebra, liveness, counts, coefficients and
degrees. The unbounded reduction is the proof above with its explicit inherited
compiler, ordinary-rank, and K215 calibration boundaries. This work is AI-assisted;
no independent human review or kernel-checked consistency theorem is claimed.
