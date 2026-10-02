# The positive-complement86 candidate accepts every actual compiler input

The [positive-complement86 source](complete75_positive_complement86_obstruction.md)
has infinitely many full positive nineteen-coordinate zeros for **every positive
input on every actual modified helical compiler slice**. In particular, it accepts
x=1 for the exact compiled machine whose ordinary-input language is empty.
This refutes this candidate's accepted-language claim, beyond the earlier
scalar-contract failure of positive restoration.

The polynomial is unchanged: **86=48M+38A**, nineteen positive witnesses,
exact degree203; its certificate has85 operations and one comparison. All eight
factors in the new family equal1, and its packed index satisfies R>q^4, with
C=0 and negative input Pell root. The supplied complement QF exceeds q, so the
reconstructed old coordinate F_old=q−QF is negative. The established75
certificate and87 polynomial remain unchanged. This theorem concerns this
specific positive-complement source, not all86-operation circuits or the
different weakened-width source previously refuted.

The existence proof uses Dirichlet's theorem and irrational rotation. It gives
an effective exact recipe, without claiming to materialize the actual compiler's
large numerals, a full giant Pell zero, or all its windows. The
[checker](complete75_positive_complement86_all_input_collapse.py) and
[receipt](complete75_positive_complement86_all_input_collapse.json) separate
finite source and congruence audits from these existence arguments.

## 1. The fixed contract and the variable retained slack

Fix positive integers d,b,DC,DR,MC,MF with d odd and not divisible by3, b odd,
and B=2^d. Fix any positive ordinary input x. No further hypothesis on the
masks is needed; in particular their parity and population do not enter the
construction. The actual modified compiler has d,b powers of5 and satisfies
these hypotheses.

Choose a sufficiently large power of5, N, so that, writing

    D=dN, q=B^N=2^D, Jrep=(q−1)/(B−1),
    t=2d*x, u=t+b, M=q^2−1=3m,

we have q>=32 and q>t+2. Then D is odd, 3 does not divide D, m is odd and
3 does not divide m. The last assertion is the exact identity
v3(4^D−1)=1+v3(D)=1. Jrep is a positive integer and u is odd, at least3.
Let

    mask=(MC+q(MF+B−1))*Jrep.                         (1)

The positive-complement source uses the supplied coordinate named `F` for QF.
Its actual relevant rows are

    C=QF−Z−alpha−t,
    R=(q*QF−Z)*M+mask,
    Nt=(DC+B*DR+X)*C+QF−zplus*(q−1).                (2)

We will set C=0 and QF=Z+U, where U=alpha+t. Crucially, alpha remains a
supplied coordinate: it may grow with the main Pell index. Unlike the earlier
scalar example, neither alpha nor U is fixed in advance. Then

    R=M*((q−1)Z+qU)+mask,
    Nt=Z+U−zplus*(q−1).                              (3)

For any integer p with p=mask modulo M put W=(p−mask)/M. The two conditions
R=p and Nt=1 are equivalent to

    U=(W−(q−1)Z)/q,
    Z=q−W modulo q(q−1),
    zplus=(Z+U−1)/(q−1).                             (4)

Indeed U is integral exactly when Z=−W modulo q. Modulo q−1, its defining
equation gives U=W, so U+Z=1 requires Z=1−W. These combine to the displayed
congruence because q and q−1 are coprime. This calculation proves the converse
as well; it is not only a necessary residue test.

## 2. Choose a projection modulus with two coprimality properties

Choose e with

    e=1 modulo3D, e=3 modulo4, e>=3D, X=2^e.          (5)

These conditions are compatible because 3D is odd. They imply gcd(e,D)=1,
3 does not divide e, q^3 divides X, and

    gcd(X+1,M)=3, v3(X+1)=1.                         (6)

For the gcd, a common divisor divides
2^gcd(2e,2D)−1=3; both original integers are divisible by3. The valuation
follows from v3(2^e+1)=1+v3(e) for odd e.

We choose Y=q^3*s, s positive, such that

    A=Y(X+1)+2=−1 modulo M,
    H=4A−5=3*ell,
    ell is prime, ell=2 modulo3, ell>3M.             (7)

Here is the full prime-progression argument. Set

    Cprime=4q^3(X+1)/3,
    [q^3(X+1)/3]*s0=−1 modulo m.

The latter coefficient is a unit modulo m by(6). For s=s0+m*z we obtain
ell=Cprime*s+1=−3 modulo m. Its first term is coprime to its difference:
it is1 modulo every prime divisor of Cprime and coprime to m, because
3 does not divide m. Also Cprime*m is a unit modulo3. Restrict z to the
single class modulo3 making ell=2 modulo3. The resulting progression still
has coprime first term and difference. Dirichlet's theorem provides arbitrarily
large primes in it. Choose one with s>=1 and ell>3M. Then(7) holds.
This is the same elementary prime progression used in the older collapse
construction, with a different role in the subsequent CRT.

Define the genuine source parameters

    a=Y(X+1), A=a+2, Delta=A^2−1,
    E=XY, P=2XY^2+1, T=2(ell−1).                    (8)

Fermat's theorem modulo ell and evenness of T modulo3 give 2^T=1 modulo H.
The choices above have two useful consequences:

    gcd(T,M)=1,          gcd(H,q(q−1))=1.            (9)

To prove the first, ell−1=−4 modulo m, while m is odd; hence ell−1 is
coprime to m. Also ell−1=1 modulo3. Since M=3m is odd, multiplying by2
changes neither assertion. For the second, H=3ell is odd, q=2^D=2 modulo3,
and ell>3M>q−1. Thus neither3 nor ell divides q(q−1).

Both coprimality properties are established for the actual compiler widths;
they are not assumptions about a conveniently selected scalar mask.

## 3. Pay the input root and both outer congruences

Write chi_A(v)+psi_A(v)*sqrt(Delta)=(A+sqrt(Delta))^v. At the fixed odd
input index u define

    chi_v=chi_A(u), kappa=psi_A(u),
    delta=(kappa−u)/Delta, Fv=chi_v+a*kappa.          (10)

For odd u, psi_A(u)=u modulo Delta, by the Pell recurrence modulo A^2−1.
Also psi_A(u)>u for A>=2,u>=3. Hence delta is a positive integer.
All data in(10) are fixed before choosing the main index.

Let L=lcm(T,4). By(9), L is a unit modulo M. Solve

    p_base=e modulo L, p_base=mask modulo M.        (11)

This has a positive solution, explicitly
p_base=e+L*((mask−e)*L^(-1) modulo M). The first congruence gives
p_base=3 modulo4. Put W_base=(p_base−mask)/M. By the second part of(9),
choose a fixed positive integer rho satisfying

    H*rho=q−W_base−Fv modulo q(q−1),
    Z=Fv+H*rho.                                    (12)

Then freeze these congruences and the first-index residue with

    S=lcm(L,M*q*(q−1),E),
    p=p_base+S*r, r>=0.                            (13)

The value W=(p−mask)/M changes by a multiple of q(q−1), so the fixed Z
continues to satisfy(4). Define U,alpha,QF,zplus by

    U=((p−mask)/M−(q−1)Z)/q,
    alpha=U−t, QF=Z+U, zplus=(Z+U−1)/(q−1).         (14)

All are integers. U increases linearly to infinity. Restrict to a sufficiently
large tail so that U>t, QF>q and p>q^4. Thus alpha,QF,zplus are positive,
R=p and Nt=1 exactly. The input expression in the literal source is

    C−Z+a*kappa+rho*H=−chi_v.

Its norm is1, with the required input index kappa=u+delta*Delta. DC and DR
have disappeared only because their actually computed multiplier C is zero.
No transport row or input equation is omitted.

For clarity, the general residue obstruction before the convenient choice(9)
is exactly

    gcd(H,q(q−1)) divides q−W_base−Fv.               (15)

This is necessary and sufficient for a rho class in(12). Once this class and
the first CRT exist, positive rho and eventual positive alpha are automatic.
The prime construction proves that(15) holds for every input and every mask
by making its gcd equal1.

## 4. The shared main quotient and both strict ratios

The Pell projection recurrence, with initial values1,2, gives

    chi_A(p)−a*psi_A(p)=2^p modulo H.

Since p=e modulo T and X=2^e, the main quotient

    c=psi_A(p), gamma=(chi_A(p)−a*c−X)/H             (16)

is integral. It exceeds the fixed rho for a sufficiently large tail. More
explicitly, for p>=2,

    chi_A(p)−a*c=2c−psi_A(p−1)>c, c>=2p.

It is enough to require p>X+rho*H. Then gamma*H>c−X>rho*H, and
sigma=gamma−rho is a positive integer. Thus the actual shared quotient
rho+sigma reconstructs the main root chi_A(p). This argument does not replace
it by a free independent quotient.

As S is divisible by E and p is odd, set

    N0=E/2, n0=(p_base+1)/2 modulo N0.

Every n=n0 modulo N0 has 2n=p+1 modulo E. Because P=1 modulo E,
psi_P(n)=n modulo E. Consequently

    k=2psi_P(n), h=(k−p−1)/E                        (17)

is integral. It remains to satisfy kY<c<k(Y+1) while retaining these two
index progressions.

Put lambda_A=A+sqrt(A^2−1), lambda_P=P+sqrt(P^2−1), and

    theta=log(lambda_A)/log(lambda_P),
    beta=log(sqrt(P^2−1)/(2Y*sqrt(A^2−1)))/log(lambda_P),
    h0=log((Y+1)/Y)/log(lambda_P).

The actual fixed parameters have A<P<2A^2−1, so1/2<theta<1. Delta is odd,
whereas v2(P^2−1)=e+2v2(Y)+2 is odd. Thus the two real quadratic fields
are distinct. If theta were rational, equal positive integer powers of their
units would lie in the intersection, hence in the rationals, which is
impossible for a positive power of either nontrivial quadratic unit. Therefore
theta is irrational.

Along(13), the rotation step S*theta/N0 is irrational. Every tail therefore
has infinitely many hits with

    h0/(3N0)<frac((p*theta+beta−n0)/N0)<2h0/(3N0).

Take n=n0+N0*floor((p*theta+beta−n0)/N0). It lies in the required residue
class and satisfies h0/3<p*theta+beta−n<2h0/3. The dominant Pell ratio lies
between Y*((Y+1)/Y)^(1/3) and Y*((Y+1)/Y)^(2/3). The exact ratio c/k differs
by the factor (1−lambda_A^(-2p))/(1−lambda_P^(-2n)). The explicit conjugate
margin in the [outer-family proof, Sections3–4](complete75_weakened86_infinite_outer_family.md)
shows that once both error terms are below1/[12(Y+1)],

    kY<c<k(Y+1).                                    (18)

Every tail has infinitely many such exact integer hits. Also n/p tends to
theta, so n<p<2n eventually. For n>=2, psi_P(n)>n; hence k>2n>=p+1 and
the integer h in(17) is positive. Define

    eta=c−kY, zeta=k(Y+1)−c,
    tau_gap=chi_P(n)−XY^2*k=psi_P(n)−psi_P(n−1).      (19)

These are positive. They recover k,c and the positive first Pell root exactly.
The factor Nk=k−R−hE is1. The corrected first-gap identity in(19) uses
k=2psi_P(n) and P−1=2XY^2.

## 5. All five auxiliary coordinates and the full zero

We have p=3 modulo4, A>=2 and c=psi_A(p). The canonical normalized lift in
[normalized87, Section3](complete75_normalized_strong87.md#3-canonical-completeness-and-the-additional-divisibility)
applies with no assumption that X=2^p or p<q^4. Set

    m_aux=2cp, f=chi_A(m_aux), t_aux=psi_A(m_aux),
    i=t_aux/c^2, Taux=Delta*t_aux,
    V=chi_Taux(p)/Taux, y_aux=psi_Taux(p),
    o=(V+c)/f, j=(V+p)/c.                           (20)

The cited divisibility and quotient identities prove that f,i,j,o,y_aux are
positive integers. The normalized strong factor and auxiliary factor are1,
and V−jc=−p. Together with k−hE=p+1 this makes the coupled linear factor1.
This supplies the full normalized strong condition, not merely a rank or
residue proxy.

All nineteen supplied positive coordinates are now specified:

    Jrep from Section1; QF,alpha,zplus from(14);
    f,h,i,j,o from(17),(20); s=Y/q^3,w=X/q^3;
    tau_gap,eta,zeta from(19); y_aux from(20);
    Z,delta,rho from(10),(12); sigma=gamma−rho from(16).

In literal source order, the first, main, input, auxiliary, index, transport,
strong and coupled-linear factors all equal1. Their product minus1 is zero.
The source checker verifies the complete eight-factor map with independent
root placeholders and exact rational divisions, so this conclusion concerns
the complete emitted86-operation polynomial.

The family contains infinitely many distinct positive tuples: p=R is
unbounded, while q,X,Y,rho,Z are fixed. In particular R>q^4 and QF>q on the
chosen tail. The restored old F=q−QF is negative. This proves an accepted-input
failure rather than merely failure to recover the old canonical auxiliary
choice.

## 6. An actual compiled false-input slice

The [frozen rejecting compiler](complete75_weakened86_rejecting_compiler.md)
gives an exact finite modified helical compiler recipe for a machine with
states start,loop,halt and tape alphabet0,1,2. Every start transition enters
loop; every loop transition preserves its symbol, head and state. Its first
start/1 transition writes2 without moving, as required by the marker convention.
The halt state is unreachable on every input, so its ordinary language is empty.
This is a transition invariant, independent of bounded simulation.

Its complete alphabet of18 tiles and lazy Start0/End1 window enumeration has
12,719,417,040 allowed windows. Applying the actual modified constant export,
without materializing its billions-long list, gives

    b=5^17, L=5^18, d=bL=5^35,
    B=2^d, with the actual MC,MF,DC,DR polynomial recipes.

The finite recipe and its completeness were proved in the frozen packet.
Here its machine invariant and compressed layout are rechecked. We reuse its
compiler construction only; that packet's arithmetic collapse concerned a
different weakened86 source and is not an assumption of the present proof.

These d,b satisfy Section1, regardless of the large mask values. The present
theorem therefore gives infinitely many full positive zeros at x=1 on this
actual rejecting program slice, and indeed at every positive x. The same
argument applies to every modified helical program export, since its d,b are
powers of5. Every such positive-complement slice accepts all positive integers;
any intended language omitting an input is misrepresented.

## 7. Reproducible evidence and its scope

The checker leaves the candidate source unchanged and records its source hash,
86=48M+38A count, nineteen-coordinate domain and inherited exact degree203.
It checks four symbolic complete maps and256 exact rational eight-factor/output
maps,128 signed, including q different from B. This tests all literal downstream
rows, with the actual shifted source meaning MF+B−1.

The finite prime host uses q=32,D=5,e=31,s=1673 and

    ell=156969212085403649, H=3ell.

Its primality is certified by a recursively checked Lucas certificate with48
nodes. The checker verifies the return period and both gcd properties, then
128 independent mask/input progressions and512 full congruence points.
Another7,800 residue classes check the exact criterion(15), including nonunit
gcd cases. Twenty-four width/exponent records check the coprime prime-progression
calculation;200 main-growth and128 corrected first-gap cases check the two
positivity identities. The frozen actual compiler layout and32 new semantic
traces accompany its exact loop invariant.

These finite tests corroborate algebra and congruences. They are not asserted
to contain complete positive Pell zeros or to exhaust actual compiler constants.
The infinitely many complete zeros and the actual false-input consequence are
proved in Sections1–6 using Dirichlet, rotation and the full normalized lift.
Author writer and fresh default replay both pass on the final receipt.
Independent full proof/source review and a separate fresh replay pass without
findings. Another independent binary Pell executor checks48 separately
constructed progressions, including q different from B: the actual main-root
projection modulo H, first-index congruence, outer transport integrality and
negative input-root norm all agree. These checks retain the finite-evidence
scope stated above.
