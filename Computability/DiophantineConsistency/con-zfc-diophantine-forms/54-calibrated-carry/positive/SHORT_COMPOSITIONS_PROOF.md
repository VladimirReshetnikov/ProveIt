# Positive consistency equations with a constant-cancelled norm minimum

## Result and dependency boundary

The main new short equation uses fifteen strictly positive integer unknowns,
**72 binary arithmetic operations, and exact total degree 64**. A second
version uses **70 operations and degree 80**. Retaining the older auxiliary
quotient instead gives **73 operations and degree 62**. These improve the
imported 72/80 and 74/68 points without claiming an operation record below
66, a variable-count record, global optimality, or a new kernel certificate.

Every final circuit in this directory binds all four ports to the complete
new native tuple in `../native/COEFFICIENT_BINDING.json`: beta, K0, MC, MF
mean its beta, K, MC, MF_source. Its base is 2^429959 and MF_source already
contains the B-1 shift. No port is mixed with the historical tuples used by
our inert comparison sources. The tuple is authenticated at ProveIt commit
`4b4349064a750ba6347293b55874a7f92abdd0db`.

The inherited native interface, ordinary strong-rank theorem and blank-K215
syntactic-refutation calibration remain mathematical dependencies. The new
argument below is an ordinary unbounded mathematical proof formalizable in
ZFC. Its consequence is that ZFC proves the lack of positive solutions is
equivalent to Con(ZFC); it does not prove either side unconditionally.

## 1. Literal polynomial

The fifteen positive unknowns of the 72/64 equation are

    J,F,alpha,z,f,h,i,T,s,w,r,eta,zeta,u,gamma.

Every letter below, other than those inputs and four fixed coefficients,
is only a polynomial abbreviation, not another quantified variable:

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1, D=X+ac+gamma H,
    ell=E kY,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    V=f^2(cT-R)-c, I=ic^2, A0=Delta(f^2-1),
    N0=r^2+ell(2r-k),
    N1=D^2-Delta c^2,
    Na=(V+u)^2-A0 u(2V+u),
    Nk=k-hE-R,
    Nt=(K0+w)(q-F-alpha)+(q-F)-z(q-1),
    A=N0 N1, B=Na Nk Nt, C=I^2-A0.

The equation is

    F=A^2+B(B-2)+C^2=0.                         (1)

The evaluator shares y0=V+u and computes 2V+u as V+y0. Its last six
producers after A,B,C are

    A2=A*A; Bminus2=B-2; Bfall=B*Bminus2;
    C2=C*C; sum=A2+Bfall; F=sum+C2.

The elementary cancellation

    B(B-2)=(B-1)^2-1                            (2)

saves one gate over explicitly subtracting the minimum target at the end.
Multiplication by 2, every other literal multiplication, and every binary
addition/subtraction are charged. There is no evaluation-time division,
exponentiation by a variable, square-root extraction, or hidden register
witness.

The 70/80 version uses positive tau,y instead of r,u and defines

    N0=tau^2-ell(ell+k),
    Na=A0(V^2-y^2)+y^2.

It uses the same equation (1). The 73/62 version keeps both gap variables
but changes V to c(Tf-1)-Rf^2. Its quotient slot has the older meaning.

## 2. Unconditional nonzero factors and complete soundness

Put n=XY^2>0. The integer n(n+1) lies strictly between n^2 and (n+1)^2,
so it is not a rational square. In either version put tau=ell+r for a gap
input, or use the supplied tau. The identity

    (ell+r)^2-ell(ell+k)=r^2+ell(2r-k)

shows N0=tau^2-n(n+1)k^2. Because k>0, N0 cannot be zero, independently
of every equation. Similarly Delta=(a+2)^2-1 lies strictly between
(a+1)^2 and (a+2)^2. Since c>0, N1 cannot be zero. Therefore A is a
nonzero integer and A^2>=1 at every positive assignment.

By (2), a zero of (1) satisfies

    A^2+(B-1)^2+C^2=1.

Each term is an integer square and the first is at least one. Consequently

    A=+1 or -1, B=1, C=0.                       (3)

N0 and N1 are units. N1=-1 is impossible modulo 4, since Delta is 0 or 3
modulo 4. The consecutive-product negative-Pell obstruction excludes
N0=-1: if x^2-n(n+1)t^2=-1 with n>=2 and t>0, then
nt<|x|<(n+1/2)t, and multiplication by the norm-one unit
2n+1-2 sqrt(n(n+1)) gives the smaller positive ordinate
(2n+1)t-2|x|, a contradiction to minimality. Here n>=2, since q>=2.
Thus N0=N1=1.

From C=0, A0=I^2>1. Define y0=V+u for a gap input and y0=y otherwise.
The exact auxiliary identity is

    (V+u)^2-A0 u(2V+u)=A0(V^2-(V+u)^2)+(V+u)^2.

Hence Na=I^2 V^2-(I^2-1)y0^2. Since B=1, Na is a unit. Its residue
modulo 4 is y0^2 when I is even, and V^2 when I is odd. Therefore Na
cannot be -1 and is 1. This also forces y0 nonzero: if it were zero,
I^2 V^2=1 would contradict I>1. Restore y=|y0|>0. The first root
is tau=ell+r>0 when applicable. All other supplied coordinates remain
positive. We have recovered

    N0=N1=Na=1, Nk Nt=1, I^2=Delta(f^2-1).      (4)

For the squared quotient set T_old=fT>0. The exact identity

    c(T_old f-1)-Rf^2=f^2(cT-R)-c

makes (4) a zero of the inherited ordinary six-factor polynomial

    N0 N1 Na Nk Nt [1+I^2-Delta(f^2-1)]-1.

For the old-quotient 73/62 version no T substitution is needed. Sections
3-7 of `upstream/ORDINARY_BLANK_PROOF.md` cover the common unit signs
Nk=Nt=epsilon, including the weak Cw=0 transport boundary; they recover
epsilon=1 through the ordinary strong-rank and signed auxiliary argument.
That theorem then extracts the blank computation for any authentic whole
native coefficient interface. We do not assume those signs before that
argument, and do not divide the supplied i by Delta. The new complete
native tuple is licensed by `../native/INHERITED_SEPARATED_PROOF.md`.
This proves soundness for every positive zero, not merely canonical ones.

## 3. Positive completeness and the squared modulus

Start from a finite blank-K215 halting computation. The authentic native
compiler supplies a canonical positive normalized witness. Write a0=a+2
and retain its positive multiplier j, so

    c=psi_a0(R), f^2=1+Delta j^2 c^4.

For our ordinary forms choose i=Delta j, I=ic^2. Then

    I^2=Delta(f^2-1), c divides I, f^2=1 modulo c.

All four fixed coefficients are unchanged. The authentic native low-mask
phase is R=3 modulo 4: q=B^N=0 modulo 4 and J=1 modulo 4, while
MC=2 modulo 4. The native condition
(Cw-1) AND (MC J+1)=0 forces Cw=1 modulo 4. Therefore
G=q(q-F)-Cw=-Cw modulo 4 and
R=G(q^2-1)+(MC+q MF)J=Cw+2=3 modulo 4.
This is a claim about authentic recovered compiler witnesses, not arbitrary
positive input assignments.

For completeness, here is the strengthened auxiliary construction itself.
Define integer polynomials Q_j by

    Q_0(X)=1, Q_1(X)=4X-3,
    Q_(j+1)(X)=(4X-2)Q_j(X)-Q_(j-1)(X).

The Pell recurrences prove, for n=2j+1,

    chi_t(n)=t Q_j(t^2),
    Q_j(0)=(-1)^j n,
    Q_j(1-a0^2)=(-1)^j psi_a0(n).               (5)

The last identity follows because the odd-index psi sequence satisfies
the same second-order recurrence after substitution and sign reversal;
the initial values are 1 and 4a0^2-1. Thus (5) consists of integer
polynomial identities and holds modulo the square modulus f^2.

Put S=I and define

    V=chi_S(R)/S, y=psi_S(R).

The quotient is integral by (5). Since S^2=Delta(f^2-1), we have
S^2=1-a0^2 modulo f^2. Since (R-1)/2 is odd, (5) gives

    V=-c modulo f^2, V=-R modulo c.

Also gcd(c,f)=1 and f^2=1 modulo c. Consequently

    T_new=(V+c+Rf^2)/(cf^2)                    (6)

is a positive integer: its numerator is divisible by f^2 and c, which
are coprime. Equation (6) is exactly V=f^2(cT_new-R)-c. The Pell
identity gives

    S^2 V^2-(S^2-1)y^2=1.

Moreover R>=3 and S>1 imply
V>=chi_S(3)/S=4S^2-3>1. Thus

    y^2-V^2=(V^2-1)/(S^2-1)>0,

so u=y-V is a positive integer. The first norm likewise gives
r=tau-ell>0 because tau^2-ell^2=ell k+1>0. Retain all other canonical
positive coordinates. For the 73/62 old-quotient version use
T_old=fT_new, still positive. The recovered tuple has A=B=1 and C=0,
so (1) vanishes. No claim is made that an arbitrary older quotient is
divisible by f: only the newly reconstructed auxiliary witness is used.

Combining this with Section 2 proves positive existence equivalence in
both directions. The K215/refutation calibration and negation yield the
stated ZFC-provable unsolvability/Con(ZFC) equivalence.

## 4. Exact operation and degree certificates

All metrics are for the displayed fixed polynomial with the new native
coefficient tuple. Set q0=beta J, k0=eta+zeta and

    E0=w s q0^4, c0=k0 s q0^3,
    ell0=k0 w s^2 q0^7,
    T0=w(q0-F-alpha)-z q0.

These are the relevant top homogeneous forms. The exact main-norm
identity, with Z=X+gamma H, is

    N1=2acZ+Z^2-Hc^2.

It has degree18 and leader 8 gamma E0^2 c0. The remaining leaders are:

- Ungapped N0: degree22, leader -ell0^2.
- Gap N0: degree12, leader ell0(2r-k0).
- Squared-modulus V: degree8, leader c0 T f^2.
- Old V: degree7, leader c0 T f.
- A0: degree14, leader E0^2 f^2.
- Ordinary C: degree22, leader i^2 c0^4.
- Nk: degree7, leader -h E0; Nt: degree2, leader T0.
- Squared-modulus ungapped Na: degree30, leader E0^2 c0^2 T^2 f^6.
- Squared-modulus gap Na: degree23, leader -2 E0^2 c0 T f^4 u.
- Old-quotient gap Na: degree22, leader -2 E0^2 c0 T f^3 u.

For 72/64, the degrees of A,B,C are 30,32,22. The only degree64
term is B^2. Its leader is

    4 h^2 E0^6 c0^2 T^2 f^8 u^2 T0^2.

In particular the monomial

    J^32 h^2 eta^2 w^6 s^8 T^2 f^8 u^2 z^2

has nonzero coefficient 4 beta^32. Thus the claimed degree is attained.
For 73/62 the same statement holds with f^6 instead of f^8.
For 70/80 the degrees are 40,39,22, and the sole degree80 term is A^2,
with leader 64 gamma^2 E0^4 c0^2 ell0^4. The coefficient of
J^50 gamma^2 eta^6 w^8 s^14 is 64 beta^50, nonzero.

The literal DAG ledger is:

| Circuit | Gates | Multiplications | Additions | Subtractions | Exact degree |
|---|---:|---:|---:|---:|---:|
| p66_degree157.json (inherited formula) |66|38|15|13|157|
| p70_degree80.json |70|39|17|14|80|
| p71_degree78.json |71|40|17|14|78|
| p72_degree64.json |72|40|18|14|64|
| p73_degree62.json |73|41|18|14|62|
| p68_degree101.json |68|38|16|14|101|
| comparisons/p70_degree84.json |70|39|17|14|84|
| comparisons/p73_degree68.json |73|40|18|15|68|

The 71/78 version takes just the first gap. The 70/84 ordinary product
is dominated by 70/80 and is retained only as a comparison. The 73/68
normalized-minimum composition is dominated by the new 72/64 result.

The ordinary product variants use the same six factors and
Ns=1+I^2-A0. At a product zero, Ns is a unit, and Ns=-1 is impossible
modulo 4 because A0 is 0 or 1 modulo 4. Thus Ns=1 and Section 2 applies.
Canonical completeness is the same. Their degrees are the sums of their
six factor degrees: 22+18+30+7+2+22=101 and
12+18+23+7+2+22=84. All factor leaders are nonzero, so the total degrees
are attained in the integral polynomial ring.

## 5. The requested 73/68 composition

For direct comparison with the two imported 74/68 circuits, use ungapped
positive tau,y, squared V, and normalized strong factor
Ns=f^2-Delta I^2. Its polynomial is

    N0^2+Na^2+Ns^2+(N1 Nk Nt-1)^2-3.

N0 is unconditionally nonzero as above. Ns cannot vanish, because Delta
is nonsquare and I>0. Na cannot vanish either: at f=1 it is y^2>0;
at f>=2 it has form A0 V^2-(A0-1)y^2 with A0>=2, and a zero would
make the reduced fraction (A0-1)/A0 a rational square. Both consecutive
positive integers A0-1 and A0 would then be squares, impossible.
Thus its three norm squares are all at least one. A zero forces all
three norms to be units and N1 Nk Nt=1. The first norm cannot be -1;
Ns cannot be -1 modulo4. Once Ns=1, A0=(Delta I)^2, so Na cannot be -1
modulo4. This recovers the normalized source. Completeness uses Section
3 with S=Delta I and the canonical normalized i, not the ordinary i.
Only Ns^2 reaches degree68; its leader is

    i^4 w^4 s^12 k0^8 q0^40.

The gate saving from each appropriate imported 74/68 construction is the
squared quotient or the norm-minima substitution, respectively. It is a
valid intermediate comparison, not the recommended final tradeoff.

## 6. Why the squared quotient does not directly shrink the 11/12-variable norm

The earlier compressed eleven/twelve-positive construction recovers the
square root f of Dstrong=1+Delta i^2c^4 from its occurrence inside
V=cTf-c-R Dstrong. After replacing T_old by fT, the auxiliary expression
becomes Dstrong(cT-R)-c and no longer contains that square root. Deleting
the f branch therefore deletes a genuine equation, not a redundant radical.

For an explicit small Pell-fiber counterexample to that inference, take
a0=2,R=3,c=15,i=1. Then S=675,
Dstrong=151876 is nonsquare, T=1, V=1822497 and y=1822499. Nevertheless
c=psi_2(3), the main Pell root is26, and
S^2 V^2-(S^2-1)y^2=1 with V=Dstrong(cT-R)-c. This is not claimed to
be a compiler zero; it demonstrates exactly the lost strong-square
condition. No new eleven/twelve-variable improvement is asserted here.

## 7. Independent reproducibility

`build_short.py` is newly authored and imports no upstream executable.
`check_short.py` imports neither the builder nor upstream programs. It
checks all four compressed and raw native payload hashes; every DAG,
operation count, supplied-port liveness; 1200 independent direct-formula
evaluations; 72 affine univariate full-polynomial degree replays using
actual bound coefficient residues over three primes; five exact Pell
reconstruction examples; and the concrete radical-coupling obstruction.
Both ordinary and optimized Python runs give identical receipts.

These finite diagnostics corroborate the formulas and implementation.
They neither replace the universal proofs above nor certify the inherited
compiler/rank theorem in a formal kernel. No consistency witness has been
searched for, found, or assumed.

## 8. Retained 66-operation comparison

The root-directory p66_degree157.json independently evaluates the inherited
66-gate polynomial, rebound as a whole to the new native tuple. It is not
claimed as a new formula. Its auxiliary coefficient is Q=(Delta i c^2)^2,
its scaled strong factor is Delta f^2-Q, and its output is

    N0 N1 [Q(V^2-y^2)+y^2] Nk Nt (Delta f^2-Q)-Delta.

The inherited proof in upstream/SQUARED_MODULUS_PROOF.md applies on the
new authentic native interface, including the verified R=3 modulo4 phase.
A direct bridge avoids depending on an unquoted normalized theorem:
since Delta>0, divide the zero equation by Delta in the proof (not in the
polynomial evaluator). The six resulting integer factors are units, with
normalized strong factor f^2-Delta i^2c^4. Modulo4 and the negative-Pell
obstruction force all four norm units to +1. Set i_ordinary=Delta*i and
T_old=fT. Then I_ordinary=Delta*i*c^2 has square
Delta(f^2-1), and its auxiliary coefficient equals the retained Q. Thus
this tuple solves the ordinary product in Section2, with the two remaining
unit signs handled by the same inherited ordinary rank argument.
Conversely a canonical normalized native witness, with the reconstructed
T,y of Section3 and its original normalized i, makes this scaled product
zero. This establishes both directions on the new tuple independently
of the historical package36 coefficient values.

Its six factor degrees are22,18,62,7,2,46, totaling157. With the notation
of Section4 its leading form is

    -8 q0^91 h gamma i^4 k0^13 w^13 s^26 T^2 f^4 T0.

Every factor is nonzero in the polynomial ring, and beta>0, so the degree
is exact. The immutable incoming DAG is retained as an inert source
upstream/INHERITED_P66.json. The active independent DAG has the same
66 live operations:38 multiplications,15 additions,13 subtractions.
