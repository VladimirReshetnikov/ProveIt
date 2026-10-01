# Supplying the positive complement q−F does not restore its upper bound

The [literal86-operation candidate](complete75_positive_complement86_obstruction.py)
deletes one subtraction from the [established normalized87 source](complete75_normalized_strong87.md)
by supplying QF=q−F as a positive coordinate. Every old positive zero has
QF>0. The converse fails: this packet gives an infinite family of **complete
positive nineteen-coordinate zeros** of the new source, with all eight factors
exactly1, but

    QF>q,       R>q^4,       C=0,       mu<0.

The reconstructed old coordinate F=q−QF is negative. Thus the retained
norms, both strict ratios, full normalized strong condition, masks,
transport, and ordinary-input equations do not restore the omitted bound.
This is a different obstruction from the previously refuted weakening:
here the packed main index R is positive and unbounded.

The family uses explicit **scalar mask-contract data**, not an exported
universal program. No actual compiled false-input instance or failure of
the candidate's accepted-language projection is claimed here. What fails
is the proposed positive-coordinate restoration and its inherited
four-field bound. The established75/87 results are unchanged, and this is
not a statement about all86-operation circuits.

The new circuit costs **86=48M+38A**, with19 positive witnesses and exact
degree203. Its certificate costs85=48M+37A and has one comparison. These
are counts for the candidate, not a new universal bound. The
[receipt](complete75_positive_complement86_obstruction.json) gives the full
schedule, exact seed and interval certificates. No enormous Pell witness
integer is claimed to have been materialized.

## 1. The guarded one-gate change and exact identity

In the normalized87 source, the supplied positive coordinate F occurs
only in

    q_minus_F=q−F.

Delete this subtraction and replace its uses by a supplied positive QF.
The source retains the historical coordinate name `F` for QF; the old
meaning is denoted F_old below. All other coordinates, constant inputs,
factors and comparisons remain unchanged. The guard checks this exact
private use and the literal source closure. Every emitted gate reaches
the final output.

For arbitrary integer assignments, set

    F_old=q−QF.                                       (1)

Every surviving register, factor and the complete polynomial then equals
the old one. This is an exact affine coordinate identity, since
q=(B−1)Jrep+1 is affine in Jrep with fixed B. It makes no positivity claim
for F_old. Conversely QF=q−F_old is positive at every genuine old positive
zero: the established theorem gives F_old+Z<q. Hence the old accepted
relation embeds into the candidate, but (1) is not a positive inverse.

With t=2d*x, the changed outer definitions are

    C=QF−Z−alpha−t,       W=C−Z,
    R=(q*QF−Z)(q^2−1)+(MC+q(MF+B−1))Jrep,
    Nt=(K0+X)C+QF−zplus*(q−1),      K0=DC+B*DR.        (2)

These are the actual unchanged downstream rows under the alias. No
packing equation or upper bound is inserted for free.

The factor degrees remain14,22,42,64,9,5,38,9. The parent's exact
cancellation identities and upper-bound argument still apply; the highest
homogeneous term is its nonzero degree203 form with only

    C_top=QF−Z−alpha−2d*x

in place of the old C_top=(B−1)Jrep−F_old−Z−alpha−2d*x.
Two weighted polynomial specializations in the checker attain
that degree and exact leading coefficient. The witness domain changes;
the degree statement does not imply correctness of the candidate.

## 2. Fixed scalar constants and the negative input root

Fix

    B=q=16, Jrep=1, d=4, b=1, x=1,
    MC=6, MF=12, alpha=3, w=8, s=1.

DC and DR may be any positive integers. These scalar data obey
0<MC,MF<B−1, MC=2 mod4, MF=4 mod8 and
popcount(MC)+popcount(MF)=d. No complete compiler export is inferred from
those conditions.

The fixed main/first quantities are

    X=w*q^3=32768, Y=s*q^3=4096, E=XY=134217728,
    a=Y(X+1)=134221824, A=a+2=134221826,
    Delta=A^2−1, H=4a+3=536887299,
    P=2XY^2+1=1099511627777,
    M=q^2−1=255, mask=MC+q(MF+B−1)=438.              (3)

As usual chi_A(v)+psi_A(v)*sqrt(Delta) is the vth power of
A+sqrt(Delta). Set u=2d*x+b=9 and define the fixed positive integers

    chi_v=chi_A(9), kappa=psi_A(9),
    delta=(kappa−9)/Delta, Fv=chi_v+a*kappa.           (4)

The odd-index congruence psi_A(9)=9 modDelta and strict Pell growth prove
that delta is a positive integer. The checker evaluates this small-index
pair exactly. For a future positive rho put

    Z=Fv+rho*H, QF=Z+11, zplus=(Z+10)/15.            (5)

Then C=0 and W=−Z. When zplus is integral, Nt=1 for every DC,DR.
Moreover the actual input expressions become

    index_rhs=9+delta*Delta=kappa,
    mu=W+a*kappa+rho*H=−chi_v.

Their norm is exactly1, despite the negative root. With (5), the actual
packed index is

    R=255(15Z+176)+438.                              (6)

Thus R grows linearly in rho and remains positive. This construction
retains the additive main quotient rho+sigma; it does not use the
independent or multiplicative gamma candidates.

## 3. An exact progression makes R the main Pell index

The integer T_H=2753268 satisfies

    2^T_H=1 modH.                                    (7)

Only this directly checked return identity is needed, not its minimality
or a primality/factorization assertion. Start with

    rho0=2, Z0=Fv+2H,
    R0=255(15Z0+176)+438,
    L=255*75*H=10267969593375.

The exact residue Z0+10=0 mod15 holds. Increasing rho by5 preserves this
transport congruence and increases R by L. Since gcd(L,T_H)=3 and
15−R0 is divisible by3, solve

    R0+L*z=15 modT_H.

The least nonnegative solution is z0=143215. Put

    p0=R0+L*z0
      =27689153732231122698612582020560843427585236025554359211783055917956507500708943,
    S=lcm(L,T_H,E,4)=316199877967503874326528000,
    p=p0+S*t,                 t>=0.                 (8)

Every such p is3 modulo4. Define

    Z=(p−438−255*16*11)/(255*15),
    rho=(Z−Fv)/H, QF=Z+11, zplus=(Z+10)/15.          (9)

By construction these are positive integers, rho>=2, and R=p. Also

    p>q^4,       0<rho*H<Z<p,       QF>q.

The ordinary Pell projection recurrence gives
chi_A(p)−a*psi_A(p)=2^p modulo H. Equations(7)–(8) imply
2^p=2^15=X modulo H. Thus, with c=psi_A(p),

    gamma=(chi_A(p)−a*c−X)/H                          (10)

is integral. It strictly exceeds rho: for p>=2,A>=3, c>=2p and

    chi_A(p)−a*c=2c−psi_A(p−1)>c.

The bound c>=2p follows from psi_A(1)=1, psi_A(2)>=6 and
the increasing positive first differences. Since every p in(8) is
greater than X, gamma*H>c−X>p>rho*H.
Therefore sigma=gamma−rho is positive. This establishes the genuine
shared main quotient rho+sigma=gamma before the ratio construction.

Freeze the first-index residue by setting

    N=E/2=67108864, n0=14238248,
    n=n0 modulo N.

Since S is divisible by E and 2n0=p0+1 modE, every such n satisfies
2n=p+1 modE. Also P=1 modE, hence psi_P(n)=n modE. For
k=2psi_P(n), the integer

    h=(k−p−1)/E                                      (11)

will be positive at all sufficiently large ratio hits constructed next.
There is no unrestricted period search hidden in these explicit constants.

## 4. Infinitely many actual ratio hits in both progressions

Write lambda_A=A+sqrt(A^2−1), lambda_P=P+sqrt(P^2−1), and

    theta=log(lambda_A)/log(lambda_P).

The fixed constants satisfy A<P<2A^2−1, so1/2<theta<1.
The square classes of the discriminants differ: Delta=A^2−1 is odd,
whereas v2(P^2−1)=41 is odd. Thus their two quadratic fields are
distinct. A rational theta would give equal positive powers of the two
units, a rational number in the intersection of these fields; its
nonzero irrational component excludes this. Hence theta is irrational.

Use the same explicit conjugate-error argument as the
[infinite outer-family proof, Sections3–4](complete75_weakened86_infinite_outer_family.md),
now with the additional n residue. Put

    beta=log(sqrt(P^2−1)/(2Y*sqrt(A^2−1)))/log(lambda_P),
    h0=log((Y+1)/Y)/log(lambda_P).

For p from(8), consider

    t_p=(p*theta+beta−n0)/N.

Its rotation step S*theta/N is irrational. Every tail of the progression
therefore has infinitely many terms with

    h0/(3N)<fractional_part(t_p)<2h0/(3N).

Set n=n0+N*floor(t_p). Then n=n0 modN and
h0/3<p*theta+beta−n<2h0/3. The dominant Pell ratio lies strictly between
Y*((Y+1)/Y)^(1/3) and Y*((Y+1)/Y)^(2/3). The exact ratio c/k differs
by (1−lambda_A^(−2p))/(1−lambda_P^(−2n)). Once p,n are sufficiently
large, each conjugate term is less than1/[12(Y+1)]; the explicit margin
in the cited proof then gives

    kY<c<k(Y+1).                                     (12)

This is a proof of infinitely many exact integer ratio hits, not a scan
or floating-point assertion. Along them n/p tends to theta, so eventually
n<p<2n. For n>=2, psi_P(n)>n, hence k>2n>=p+1 and (11) is positive.
The two supplied ratio slacks

    eta=c−kY, zeta=k(Y+1)−c

are positive integers, sum to k and reconstruct c exactly. The first-root
slack is likewise positive:

    tau_gap=chi_P(n)−XY^2*k=psi_P(n)−psi_P(n−1)>0.

It reconstructs the exact first norm, with no bound on R used in this
construction.

## 5. Completing all nineteen positive coordinates

Retain (3)–(12). The main and first norms are1, the input norm is1,
and (11), R=p give Nk=k−R−hE=1. The transport factor is1 by(5).
It remains to supply the five normalized auxiliary coordinates.

Here p=3 mod4 and c=psi_A(p). The canonical construction from
[normalized87, Section3](complete75_normalized_strong87.md#3-canonical-completeness-and-the-additional-divisibility)
uses only these main data and gives

    m=2cp, f=chi_A(m), i=psi_A(m)/c^2,
    Taux=Delta*psi_A(m), y=psi_Taux(p),
    V=chi_Taux(p)/Taux,
    o=(V+c)/f, j=(V+p)/c.                            (13)

All five supplied coordinates f,i,j,o,y are positive integers. In
particular c^2 divides psi_A(2cp), by expanding the2c-th power of
chi_A(p)+c*sqrt(Delta). The canonical odd-minus identities prove both
congruence quotients in(13), the auxiliary norm and the normalized strong
norm. This construction does not assume p<q^4 or X=2^p. Its exact local
hypotheses A>=2, p=3 mod4, c=psi_A(p) hold here.

The auxiliary factor is therefore1, the strong factor is1, and

    L=V−jc+k−hE=−p+(p+1)=1.

Together with (9)–(12), this lists every supplied positive coordinate:

    Jrep=1, QF=Z+11, alpha=3, zplus=(Z+10)/15,
    f,h,i,j,o from(11),(13), s=1,w=8,
    tau_gap,eta,zeta from Section4, y from(13),
    Z,delta,rho,sigma from(4),(9),(10).

Thus all eight factors are1 and the complete86 polynomial vanishes.
The original F_old=q−QF is strictly negative at every family member.
C=0 is also incompatible with a genuine old positive zero: its Nt=1
would give q−F_old−zplus(q−1)=1, while F_old,zplus>=1 make that quantity
at most0. The candidate's full positive zeros consequently lie outside
the claimed positive inverse, not merely outside an arbitrary canonical
choice of native auxiliaries.

## 6. A concrete exact recipe and reproducible checks

The checker includes the following fully specified ratio hit:

    t=2827864894933348,
    p=27689153732231122698612582020560843428479406560240872014501246148159455756452943,
    n=18909695711339583511386628105482078268425333847339916462699118496112267748786728.

The progression identities are exact. Directed-integer Pell intervals
at384 and512 bits certify both strict inequalities(12); all three
512-bit intervals nest inside their384-bit counterparts. This specifies
a complete nineteen-coordinate positive zero through(4),(9)–(13).
The actual coordinate integers are enormous and are not printed or fully
evaluated. Floating-point logarithms were used only to locate these
indices; the saved certificates and default replay use integer arithmetic.

The exact source audit substitutes the recipes into the complete literal
schedule and proves all eight factor identities symbolically, including
C=0,R=p,index_rhs=psi_A(9),mu=−chi_A(9). It also checks192 exact rational
whole-output maps,96 signed; these corroborate identities, not the
positivity/existence theorem. Separate checks cover384 arbitrary whole
source identities under(1),192 signed; two weighted exact-degree fixtures;
128 modular progression cases; and165 small Pell-growth inequalities.
No small inequality fixture is called a full compiler zero.

Run `python3 complete75_positive_complement86_obstruction.py`; `--write`
regenerates the receipt. The author writer and a separate fresh default
replay passed. All five local links and whitespace checks pass. The scalar-contract
scope remains deliberate: an actual compiled program and a false-membership
input have not been instantiated, so this packet does not by itself settle
the candidate's universal accepted-language claim.

Root independently reviewed the full proof, literal source and dependencies,
and passed a fresh default replay with no findings. Its separate executor
checked192 complete register/output maps,96 signed, and64 independently
reconstructed progression cases. Nine small canonical auxiliary fixtures
checked every quotient and norm exactly; these are local blocks, not full
compiler zeros. A separate768-bit directed-integer Pell interval audit
certified both concrete ratios. The review also checked irrational rotation,
all congruences, shared gamma>rho, h>0, positivity of all nineteen coordinates
and the explicit scalar-only scope. The trio is frozen after this review.

During complementary review, the displayed first-root identity in Section4
was corrected to psi_P(n)−psi_P(n−1). Its strict positivity is unchanged.
The literal source already used chi_P(n)−XY^2*k, so no source or receipt
change was needed.

The native-controller complementary full proof/source/dependency review and
fresh default replay also passed after that note-only correction, with no
remaining findings. Its independently rebuilt seed and progression matched.
Its own outward-rounded quadratic-ring exponentiation certified both huge
ratios at640 and896 bits, with160 exact small enclosure checks. A separate
literal executor and manual rational recipes passed192 complete eight-factor
and output identities,96 signed; four small exact canonical normalized
auxiliary blocks and another weighted degree203/leading-coefficient expansion
also passed. The review checked irrational rotation, gamma>rho, h>0, all
nineteen positive coordinates and scalar-only scope. All five links resolved;
no huge complete Pell tuple was materialized. Source and receipt were unchanged
through both independent reviews.
