# A thirteen-positive degree-126 adjunct by an auxiliary quotient

## Result and scope

This is an additional degree/operation tradeoff, not a replacement for the
frozen twelve-positive construction. It has thirteen strictly positive
integer unknowns, exact total degree **126**, and **91** live binary
arithmetic operations: 51 multiplications, 24 additions, 16 subtractions.
The late incoming parent has thirteen positives, degree132 and83 operations.
Our degree is lower, but our operation count is higher. The parent's separate
twelve-positive points242/94 and258/89 dominate our earlier twelve-positive
316/102 point in these metrics and use a smaller whole coefficient tuple.
No global optimality, kernel-checked full ZFC proof, or consistency decision
is claimed.

The complete fixed tuple is the incoming package39/44 native-window tuple,
with beta=2^590069−1, unchanged in all four ports. Its compressed payloads,
binding, compiler proof and provenance are under `coefficients/`. MF is
already shifted. The parent archive and inert parent DAG hashes are in
`PARENT_PIN.json`. The parent proof and source dependencies are preserved
under `upstream/low_degree/`; this adjunct neither executes their code nor
changes any frozen wave8 family.

## 1. Literal polynomial

Supply exactly the thirteen positive variables

    J,F,alpha,z,f,i,T,s,w,eta,zeta,y,t.

Every other letter below is a polynomial abbreviation, not a quantified
unknown. First set

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+1)(a+3),
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2,
    b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)(q-F-alpha)+q-F-z(q-1),
    U=4q^4, r=k-R-1, S=UH,
    W=U b0+H[U(t+ell)+r],
    N=(W^2+U^2G-S^2A)^2-4W^2U^2G.

These are the parent's separate main/first-Pell norm. Define

    I=ic^2, Ns=f^2-Delta I^2,
    Q=Delta(f^2-1), V=c(Tf-1)-Rf^2,
    M=a+1, C=(a+3)(f^2-1),
    Z=C(V^2-1)+(Q-1)y(2-My).

The new equation is

    P=Nt(1+N)Ns(1+Z)-1=0.                       (1)

`thirteen_positive_degree126.json` is the full literal DAG. All exponents
are fixed, and all coefficients are fixed integers.

## 2. Two elementary identities and the unit guard

Because MC=Q, the following is an exact polynomial identity, for every
integer assignment, without divisibility or positivity hypotheses:

    MZ = QV^2-(Q-1)(My-1)^2-1.                  (2)

Here the M and C in MC=Q are the two auxiliary abbreviations, not the fixed
coefficient port named MC. The JSON distinguishes them as `M` and `Caux`.
Also

    N = product_(sg,st=+/-1) [W-sg U sqrt(G)-st S sqrt(A)]

as a formal norm identity; in particular N is a square modulo4.

We use the following slightly strengthened form of the parent's elementary
negative-Pell obstruction:

**Small-negative-value lemma.** If m>=2 and 0<b<2m-2 are integers, then
x^2-(m^2-1)v^2=-b has no integer solution.

Proof. Replace x,v by absolute values. Necessarily v>0. Since
x^2=(m^2-1)v^2-b and (2m-2)v^2>b, one has
(m-1)v<x<mv. Multiplication by the norm-one element
m-sqrt(m^2-1) gives another solution whose ordinate is mv-x, a strictly
smaller positive integer. The abscissa can again be replaced by its absolute
value. Infinite descent proves the assertion. In particular b=1 gives the
usual negative-Pell obstruction for every m>=2.

Suppose (1) holds. Its four integer factors are units. The choice
1+N=-1 would give N=-2, impossible modulo4, so N=0. Since Delta=(a+2)^2-1
and a is positive already from the positive supplied variables, Ns=-1 is
excluded by the lemma with m=a+2,b=1. Thus Ns=1 and

    f^2-Delta I^2=1,  Q=(Delta I)^2.

Put m=Delta I>=2. If 1+Z=-1, then Z=-2. Identity(2), with v=My-1 and
x=mV, would yield

    x^2-(m^2-1)v^2=-(2a+1).

But 0<2a+1<2Delta I-2=2m-2: indeed I>=1 and
2Delta-2-(2a+1)=2a^2+6a+3>0. The lemma excludes this alternative.
Therefore Z=0 and Nt=1. We have recovered

    Nt=1, N=0, Ns=1,
    QV^2-(Q-1)y_old^2=1,  y_old=My-1>0.          (3)

The last positivity follows from y>=1 and M=a+1>1. Thus (3) is precisely
the parent's thirteen-positive system with the old auxiliary ordinate
restored. No cancellation was made at an unchecked denominator. The order
of the argument also does not assume the transport equation prematurely.

The parent's main-norm recovery, normalized strong-rank argument and
signed auxiliary-index reconstruction now apply exactly as written in
`upstream/low_degree/PROOF.md`, Sections4–5. They give positive main and
first-Pell roots, p=R, 2n=R+1, and restore the deleted h and gamma quotients.
Consequently every solution gives a blank K215 halt and hence a finite
syntactic ZFC refutation, using the inherited compiler/calibration theorem.

## 3. Completeness and the changed meaning of y

This step is an existence reduction. It is not asserted that every parent
y_old has the required residue.

Start with a canonical normalized compiler witness of a blank K215 halt,
using the unchanged whole fixed tuple. Keep its outer coordinates, its
positive f,i, and its carrier t from the parent's Section6. Then Ns=1,
Q=m^2 with m=Delta I, and the authentic population decoding gives
R=3 modulo4. Choose new auxiliary values

    V=chi_m(R)/m,  y_old=psi_m(R).

The parent's explicit odd-index reconstruction, Section9, proves

    V=-c modulo f^2,
    V=-R modulo c,
    y_old=-1 modulo Q.

For clarity, the last assertion follows because psi_m(R) is an even
polynomial in m whose constant term is (-1)^((R-1)/2)=-1. The first two
come from the odd-index polynomial chi_m(2j+1)=m Q_j(m^2), its values at
m^2=1-(a+2)^2 modulo f^2 and at0 modulo c, and the main Pell rank R.
These are the same explicit identities and ordinary reconstruction lemma
preserved in the incoming source, not a new cofinality hypothesis.

Since gcd(c,f)=1 and f^2=1 modulo c,

    T=(V+c+Rf^2)/(cf)

is a positive integer and gives the literal V in Section1. The Pell identity
supplies QV^2-(Q-1)y_old^2=1. Because M divides Q and y_old=-1 modulo Q,

    y=(y_old+1)/M

is a positive integer. Identity(2) and M>0 imply Z=0. The outer carrier and
Nt,N,Ns are unaffected by replacing T,y. Thus (1) has a positive solution.
This proves both existence directions. Composing with the inherited
syntactic calibration proves in ZFC:

    (there is no strictly positive integer solution of P=0) iff Con(ZFC).

No consistency assumption or accepting computation is assumed by the
construction; completeness is the stated implication from an accepting
computation.

## 4. Exact total degree

Degrees count the thirteen supplied variables only; the tuple is fixed.
Write the leading homogeneous forms

    q0=beta J, Y0=sq0^3, E0=wq0Y0,
    k0=eta+zeta, c0=k0Y0, ell0=E0c0,
    U0=4q0^4, H0=4E0, I0=i c0^2,
    Nt2=w(q0-F-alpha)-zq0.

The exact main norm degree68 and leading form are inherited from the
parent's explicit polynomial cancellation identity (Section7), also checked
symbolically by this package:

    N68=4 U0^4 H0^3 ell0^3 (2t-k0).

The strong factor Ns has degree34 and leading form -E0^2 I0^2. Here
Q has degree14, M degree6, C degree8, and V degree7 with leading form c0Tf.
Both summands of Z have degree at most22. Their combined highest part is

    Z22=E0 f^2 (c0^2 T^2 f^2-E0^2 y^2),

which is a nonzero polynomial. Consequently (1) has exact degree
2+68+34+22=126, with nonzero leading form

    P126=-N68 E0^3 I0^2 f^2
              (c0^2 T^2 f^2-E0^2 y^2) Nt2.      (4)

Each displayed factor is nonzero for fixed beta>0, and the polynomial ring
is an integral domain. This is a universal upper and lower degree proof;
finite specializations are not used as upper-degree certificates.

## 5. Reproduction and limitations

Run `python3 build.py` and `python3 check.py`. The builder authenticates the
inert parent JSON before retaining its exact shared prefix. It executes no
upstream program. The independent checker verifies all13 variables and4
fixed ports are live, every gate is live and ordered, and the91-operation
count. It verifies the exact quotient, four-factor norm and parent degree
cancellation identities symbolically, checks actual payload hashes, and
runs six finite-field rays with all exact leaders from (4). It additionally
checks a finite set of odd-Pell ordinate residues. Normal and `python3 -O`
outputs agree; neither script relies on removable `assert` statements.

These computational checks verify finite transcription properties, not the
unbounded compiler theorem, global minimality, or the absence of zeros.
The retained coefficient and compiler source proofs remain dependencies.
The elementary mathematical proof above is formalizable in ZFC; no new
proof-assistant kernel certificate is asserted.
