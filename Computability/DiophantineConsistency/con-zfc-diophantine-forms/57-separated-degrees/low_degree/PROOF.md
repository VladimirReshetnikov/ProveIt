# Two separate quadratic norms: twelve positive variables at degree 242

## Scope and coefficient dependency

The recommended constructions are ordinary integer polynomials in twelve
strictly positive unknowns with exact degree/operation pairs **242/94** and
**258/89**. A companion has thirteen positive unknowns, degree 132, and 83
operations. The degree 314/91 twelve-variable form is retained as a transparent
intermediate, not a recommended frontier point. Relative to inspected ProveIt
snapshot `4b4349064a750ba6347293b55874a7f92abdd0db`, the incoming wave-7
recommended twelve-positive form has degree 897 and 108 operations. These
constructions do not reduce the smallest known positive-variable count,
prove global optimality, or decide consistency. Sections 1-8 prove the shared
intermediate and thirteen-variable companion; Section 9 gives the recommended
quotient reductions and their complete existence proofs.

Fix one whole authentic normalized native-window compiler tuple
(beta,K0,MC,MF). MF is already shifted. The supplied finite instance uses the
package 39/44 tuple with B=2^590069 and beta=B-1, as carried by the incoming
`con-zfc-sparse-pell-124c07c0b7.zip` archive. The four integer payload hashes
are recorded in CHECKS.json. All reductions below are uniform in whole
coherent tuples satisfying the inherited compiler contract. Arbitrary
port-wise changes are not authorized by this theorem.

The inherited mathematical dependencies are the native-window/Pell compiler,
the K215 syntactic-refutation calibration, canonical positive completeness,
and the standard signed auxiliary-index recovery. The latter is documented
in `38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md`, and its signed normalized
interface can be reduced explicitly to Section 5 of
`35-cancel12/sources/catalogue/25-hybrid12/upstream/ORDINARY_BLANK_PROOF.md`
by putting i_ordinary=Delta*i. The modulus idea U=4q^4 appears in the incoming
wave-7 `ConZFC_Support_Sensitive_2026-10-23.zip`, eleven/PROOF.md; the present
construction uses it with two *separate* quadratic norms. This is an ordinary
mathematical proof formalizable in ZFC, not a newly kernel-checked complete
object-language ZFC proof artifact.

## 1. Literal construction of the transparent intermediate

For the twelve-variable polynomial supply exactly

    J,F,alpha,z,i,T,s,w,eta,zeta,y,t > 0.

Every other letter is a polynomial abbreviation, not a quantified witness.
Set

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2,
    b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)(q-F-alpha)+q-F-z(q-1),
    U=4q^4, r=k-R-1, S=UH,
    W=U b0+H[U(t+ell)+r],
    N=(W^2+U^2G-S^2A)^2-4W^2U^2G.

Now put

    I=i c^2, D=1+Delta I^2, Q=(Delta I)^2, d=Q-1,
    v=cT, b=c+RD, Baux=2Qvb,
    e=Q(Dv^2+b^2)-1,
    Jaux=(e-dy^2)^2-Baux^2 D.

The equation is

    P12=Nt(1+N)(1+Jaux)-1=0.                    (12)

The named JSON `twelve_positive_degree314.json` is the literal 91-gate DAG.
All powers are fixed; all coefficients are fixed integers.

For the thirteen-variable companion, retain a positive f as an additional
supplied unknown and replace the second norm by the two Pell factors

    Ns=f^2-Delta I^2,
    Aaux=Delta(f^2-1),
    V=c(Tf-1)-Rf^2,
    Na=Aaux(V^2-y^2)+y^2.

Use instead

    P13=Nt(1+N)Ns Na-1=0.                       (13)

Its literal DAG is `thirteen_positive_degree132.json` (83 operations).

## 2. Integer units recover the system before any index argument

For every integer assignment, N is a square modulo 4. So is Jaux, because
Baux is even. If P12=0, each of the three integer factors is a unit. The
option 1+N=-1 would force N=-2, which is impossible modulo 4; the same
argument applies to Jaux. Consequently

    Nt=1, N=0, Jaux=0.                          (14)

This obtains the authentic transport interface immediately, before any
root recovery, divisor cancellation, or positivity assumption about R.
The compiler's outer-interface bounds are

    q>=16, Cw=q-F-alpha>0, 3q<R<q^4-2,
    X>=q, Y>=q^3, E>=q^4>R+2,
    k>=2, kY<c<k(Y+1).

For example Cw<=0 would imply
Nt<=q-F-z(q-1)=1-F-(z-1)(q-1)<=0, a contradiction.
These bounds make Delta,I,Q,D,c,v,b and Baux all strictly positive,
with Q>1 and Baux!=0. There is no exceptional zero-denominator branch.

For P13 the same unit argument first yields N=0 and Ns,Na,Nt in {+1,-1}.
We use the elementary negative-Pell obstruction

    x^2-(m^2-1)y^2 != -1 for integers x,y, m>=2.  (15)

Proof: take x,y nonnegative, with y>0. A hypothetical solution satisfies
(m-1)y<x<my. Multiplication by m-sqrt(m^2-1) replaces y by my-x,
a strictly smaller positive integer, and preserves the equation; take the
absolute value of the new abscissa if needed. This contradicts descent.
Thus Ns cannot be -1 (m=a+2). Once Ns=1,
Aaux=(Delta I)^2 is a square m^2 with m>=2. The equation Na=-1 is another
instance of (15), with abscissa mV. Hence Na=Nt=1. P13 therefore gives the
same normalized strong and auxiliary equations directly, with f>0.

## 3. Separate recovery of the strong root in the twelve-variable case

From Jaux=0 and Baux!=0, define the rational number

    f=(e-dy^2)/Baux.

Then f^2=D. A rational square root of an integer is an integer, so f is a
nonzero signed integer. The defining equality is exactly

    d y^2 = Q(vf-b)^2-1,                         (16)

since f^2=D and e=Q(Dv^2+b^2)-1. Also

    f^2-Delta I^2=1,
    vf-b=c(Tf-1)-Rf^2.

Thus the same normalized strong and auxiliary equations as for P13 are
recovered. No sign of f is assumed. The signed auxiliary-index theorem
uses |f| as its modulus and covers this branch. If an ordinary-strong
statement is desired, put i_ordinary=Delta*i, so that
(i_ordinary c^2)^2=Delta(f^2-1)=Q; its signed Section-5 hypotheses match
exactly. The positive ordinary coordinate remains positive.

## 4. Recover g and tau using only the first quadratic norm

Let g0=sqrt(G)>0 and tau0=sqrt(A)>0. The exact real factorization is

    N=product_(sg,st=+/-1) [W-sg U g0-st S tau0]. (17)

At this point W is strictly positive. Indeed r=k-R-1>=1-R, U>R, and
therefore t+r/U>0. The formula W=U b0+S(ell+t+r/U), with b0>0, proves it.

For a vanishing factor, write W=U g+S tau with g^2=G, tau^2=A.
Squaring the relation isolates

    2WU g = W^2+U^2G-S^2A.

Since WU!=0, g is rational, hence an integer. Then tau is rational and
an integer as well. This proof covers coincident square classes and does
not assume independent Galois sign changes.

The sign g<0 is impossible. The bounds

    tau0<ell+k,
    (b0+g0)/H > 2ac/(4a+3)>c/3>k

hold because a>1 and c>kY with Y>3. If g=-g0, then

    tau=(W+Ug0)/S=ell+t+r/U+(b0+g0)/H>ell+k>tau0,

contradicting tau^2=A. Thus g=g0>0. The sign of tau is irrelevant until
canonical completeness; |tau| is the positive first Pell root.
Reducing W=Ug+S tau modulo U gives

    U divides H(k-R-1).                         (18)

We have not canceled H, nor assumed the deleted index quotient exists.

## 5. Recover the exact indices before either deleted quotient

Put A0=a+2 and P0=2EY+1. Pell classification gives indices p,m,n>=1 with

    g=chi_A0(p), c=psi_A0(p),
    |f|=chi_A0(m), I=psi_A0(m),
    |tau|=chi_P0(n), k=2psi_P0(n).

The first-Pell discriminant EY(EY+1) has fundamental integer-coordinate
unit (P0,2). Because P0>A0 and c>k, monotonicity gives n<p.
Because c>1, p>=2 and c>=2A0>2R. Also c>2p by Pell growth.

Since c^2 divides I, strong divisibility gives p|m. Writing m=pj, the
composition formula reads

    I=c psi_g(j), psi_g(j)=j g^(j-1) modulo c.

The relation g^2=1 modulo c makes g invertible there, so c|j. Hence c|m
and m>=pc>2p. This establishes the signed auxiliary-index hypotheses
without the ordinary-strong large-c lemma or the deleted h coordinate.

For completeness of the dependency trace, let M=Delta I. Equation (16)
is M^2 V^2-(M^2-1)y^2=1, with V=c(Tf-1)-Rf^2. Its Pell index j0 is odd,
because its abscissa is divisible by M. The integer odd-index polynomials
satisfy

    chi_M(2a+1)=M Q_a(M^2),
    Q_a(1-A0^2)=(-1)^a psi_A0(2a+1),
    Q_a(0)=(-1)^a(2a+1).

Modulo |f|, M^2=1-A0^2 and V=-c. Squaring and doubling, followed by the
standard signed abscissa index reduction with 0<2p<m, gives
j0=+p or -p modulo m, hence modulo c. Modulo c, M^2=0, f^2=1 and V=-R,
so j0=+R or -R modulo c. Since 0<p,R<c/2, these congruences force

    p=R.                                        (19)

All statements here concern the recovered squares and auxiliary equation;
none uses h or the main congruence gamma yet.

Set mu=U/gcd(U,H). Since H is odd and H=3 modulo q, no prime except 3
can divide both q and H. If 3|q, then 27|Y and H=3 modulo 27, so its
3-adic valuation is exactly one. Consequently

    gcd(U,H)<=3, mu>=4q^4/3>R.

The first Pell recurrence gives k=2n modulo 4EY. Since
4EY=4w s^2 q^7 is a multiple of U, (18) gives
2n=R+1 modulo mu. But 1<=n<R implies |2n-R-1|<R<mu. Therefore

    2n=R+1,
    r=k-R-1 is divisible by 4EY, hence by E and U.

The restored h=r/E is positive: n=(R+1)/2>=25 and psi_P0(n)>n imply
r=k-2n>0. Dividing the carrier by U now gives

    g=b0+H(t+ell+r/U-tau).

Thus gamma=(g-b0)/H is an integer. It is positive because n>=2 implies
k>=4P0>X, hence c>X, and g>(a+1)c gives g-b0>c-X>0.
We have recovered the complete normalized compiler system, including
k-hE-R=1 and the positive main quotient gamma. The signed auxiliary
soundness theorem therefore supplies a blank K215 halt and hence a finite
syntactic ZFC refutation. This conclusion does not require changing a
negative f into a positive one on the same assignment.

## 6. Completeness preserves positive supplied coordinates

Start with a canonical positive normalized compiler witness for a K215 halt.
The inherited theorem gives p=R=2n-1, h>0 and gamma>0. The first-Pell
recurrence implies r=k-R-1 is divisible by U. Retain all uneliminated
coordinates, and define

    t=gamma+tau-ell-r/U.

This is an integer. Since tau^2=ell^2+ell k+1 and ell>k,

    tau-ell=(ell k+1)/(tau+ell)>ell k/(2ell+k)>k/3.

Meanwhile 0<r/U<k/U<k/3. Hence t>gamma>0. The carrier identity holds,
so N=0. For P13 the unchanged positive f and y give Ns=Na=Nt=1.
For P12 the same f is eliminated: the canonical auxiliary equality gives
e-dy^2=Baux f and consequently Jaux=0. All twelve retained supplied
coordinates are positive. Thus both existence reductions hold in both
directions. Negating and composing with the inherited refutation calibration
proves in ZFC that either displayed polynomial has no positive solution iff
Con(ZFC). No consistency assumption was used.

## 7. Exact degree by polynomial identities

Degrees count only supplied witnesses. Write

    q0=beta J, X0=wq0, Y0=sq0^3, E0=X0Y0,
    k0=eta+zeta, c0=k0Y0, ell0=E0c0,
    H0=4E0, U0=4q0^4, I0=i c0^2,
    R0=q0^3(q0-F), Nt0=w(q0-F-alpha)-zq0.

These are leading homogeneous forms. To bound N without formal-root or
numerical arguments, define the exact polynomial abbreviations

    D0=b0^2-G=X^2+2Xac-Hc^2-1,
    Z=Ut+r,
    C2=U^2 D0+2UH b0 Z+H^2(2U ell Z+Z^2-U^2 ell k-U^2).

Expanding (17), or directly squaring, gives the exact identity

    N = 4U^4 H^2 ell^2 D0
        +4U^2 H b0 ell C2+C2^2
        -4U^4 H^2 G(ell k+1).                  (20)

Here deg D0<=16, deg C2<=32. The four displayed summands have degree at
most 66,68,64,62. Only the second can reach 68. Its highest part is

    N68=4U0^4 H0^3 E0 c0 ell0^2 (2t-k0)
       =2^16 w^6 s^9 k0^3 q0^49 (2t-k0),      (21)

which is nonzero for beta>0. Thus deg N=68 exactly.

For P12, Q has degree 46, D degree 34, b degree 38 and v degree 6.
The degree 122 leader of e-dy^2 is Q0 b_lead^2, whereas Baux^2D has degree 214.
Consequently Jaux has exact degree 244, with leader

    E0^16 I0^12 R0^4.

Multiplication by N and Nt gives exact degree 68+244+2=314 and leader

    N68 E0^16 I0^12 R0^4 Nt0 !=0.              (22)

For P13, Ns has degree 34 with leader -E0^2 I0^2, and Na has degree 28
with leader E0^2 c0^2 T^2 f^4. Thus its exact degree is 68+34+28+2=132,
with leader

    -N68 E0^4 I0^2 c0^2 T^2 f^4 Nt0 !=0.       (23)

All expressions are identities or degree bounds in integer polynomial
rings; no experimental diagonal degree is used as an upper bound.

## 8. Reproducible finite checks and limits

The independently written verifier checks DAG order and liveness, all supplied
variables and fixed leaves, literal operation counts, and full univariate
polynomial evaluations at three finite primes with the actual fixed tuple.
The diagonal uses t=3x and every other variable=x, avoiding the accidental
vanishing of 2t-eta-zeta on the ordinary diagonal. Its leading coefficients
agree with (22)-(23). It independently multiplies the four radical factors
in a four-dimensional algebra, tests the mod 4 guards, and checks a finite
sample of the negative-Pell obstruction. CHECKS.json records all outcomes.
These diagnostics corroborate transcription; they do not replace Sections
2-7, the inherited compiler proofs, or the internalization into ZFC.

## 9. Recommended improvement: use the auxiliary ordinate's known residue

The degree 314 form has a particularly transparent reconstruction, but the
canonical auxiliary ordinate contains a known residue that can be removed.
The following adapter supplies two strictly better twelve-positive variants.
The positive y coordinate changes its meaning; this is an existence reduction,
not a claim that every old positive witness has the specified residue.

Let M,C be positive polynomial abbreviations with Q=MC. Define

    Z=C(Dv^2+b^2-1)+d y(2-My),
    J_M=Z^2-4C^2 Dv^2 b^2,
    P_M=Nt(1+N)(1+J_M)-1.                       (24)

Two useful choices, with no variable division in their actual definitions, are

    Full modulus: M=Q, C=1;
    Balanced modulus: M=(Delta i c)^2, C=c^2.

The balanced builder evaluates M=(Delta I)(Delta i) and Q=M c^2 to save a
multiplication. The full-modulus equation has degree 258 and 89 operations;
the balanced equation has degree 242 and 94 operations. Both use exactly the
same list of twelve positive unknowns.

### Soundness

J_M is a square modulo 4, so the same unit argument gives Nt=1,N=J_M=0.
All of M,C,v,b are positive. The rational number

    f=Z/(2Cvb)

has square D; hence it is a nonzero integer. Put y_old=My-1, a positive
integer since M>=2 and y>=1. The exact identity

    MZ=Q(Dv^2+b^2)-1-d(My-1)^2                 (25)

and Q=MC show e-d y_old^2=2Qvb f. Thus (16) holds with y_old instead of
y, and the entire signed soundness proof in Sections 4-5 applies unchanged.
No cancellation is made before positive denominators are established.

### Canonical completeness and the residue -1

The authentic compiler's population decoding gives R=3 modulo 4. This is an
inherited structural fact about the whole fixed tuple, not a claim about
arbitrary coefficient substitutions. Keep a canonical normalized witness's
outer coordinates, its f>0 and i>0. Write m=Delta I, so Q=m^2, and choose
new auxiliary values

    V=chi_m(R)/m, y_old=psi_m(R).

The odd-index Pell polynomials make V a positive integer. They give

    V=-c modulo f^2,
    V=-R modulo c,
    y_old=-1 modulo m^2=Q.                     (26)

For the first congruence use m^2=Delta(f^2-1)=1-(a+2)^2 modulo f^2 and
Q_j(1-(a+2)^2)=(-1)^j psi_(a+2)(2j+1), with j=(R-1)/2 odd. For the
second use Q_j(0)=(-1)^j(2j+1) and c|m. For the third, psi_m(R) is an
even polynomial in m; its constant term is (-1)^((R-1)/2)=-1. The recurrence
psi_m(n+1)=2m psi_m(n)-psi_m(n-1) proves both assertions by induction.

Because gcd(c,f)=1 and f^2=1 modulo c, (26) implies
V+c+Rf^2 is divisible by cf (indeed by cf^2). Therefore

    T=(V+c+Rf^2)/(cf)>0

is an integer and gives V=c(Tf-1)-Rf^2. The Pell identity supplies (16).
This construction is exactly the squared-modulus auxiliary reconstruction
lemma in the preserved wave-7 source, using its older cf quotient rather
than its stronger cf^2 quotient. No auxiliary cofinality assumption is used.

For either M|Q, (26) makes y=(y_old+1)/M a positive integer. The carrier
coordinate t remains the Section 6 value and is unaffected by replacing T,y.
Identity(25) gives J_M=0. This proves completeness of both variants.

### Degree and cost

For M=Q, deg M=46 and C=1. The two summands of Z have degrees at most 76
and 94, respectively; the latter has leading part -Q0^2 y^2. Thus J_M has
exact degree 188, its other term having degree 122, and P_M has exact
68+188+2=258. Its leading form is

    N68 Q0^4 y^4 Nt0, with Q0=E0^4 I0^2.

For M=(Delta i c)^2=Q/c^2 and C=c^2, deg M=36 and deg C=10. The first
summand of Z has degree 86 with leader c0^2 R0^2 E0^4 I0^4, whereas the
second has degree 84. The subtracted term of J_M has degree 142. Therefore
J_M has exact degree 172, and P_M has degree 68+172+2=242. Its leading form is

    N68 c0^4 R0^4 E0^8 I0^8 Nt0 !=0.           (27)

The corresponding DAGs have 89 and 94 live binary operations. The supplied
finite checker verifies both against these exact universal degree formulas,
and also tests identity(25) and the odd-Pell ordinate congruence.
