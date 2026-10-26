# Proof of the 14-positive 66/118 and 67/94 equations

## 1. Complete definitions and fixed domain

The fourteen independent unknowns, all strictly positive integers, are

    J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma.

The four fixed coefficients beta,K0,MC,MF are the entire block-mask2963
tuple at repository commit cdfea7d90176775d74c1c30afbe49fa78ade9897.
The compressed exact integers, byte encoding, hashes and source binding
are in `coefficients.json` and `coefficients/`. Their complete finite
recipe is the constant portion of `sources/block-mask2963_equation.tex`.
In particular beta=2^(47*2963)-1; MF is the shifted source mask.

Define the following polynomial abbreviations, which are not extra unknowns:

    qm=beta*J, q=qm+1, C=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
    ell=E*k*Y, c=k*Y+eta, a=E+Y,
    H=4*a+3, Delta=a^2+H, D=X+a*c+gamma*H,
    R=[qm*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    tau=E*n+k-R, V=f^2*(c*T-R)-c,
    Aaux=Delta*(f^2-1),
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=Aaux*(V^2-y^2)+y^2,
    Nt=(K0+w)*C+(q-F)-z*qm.

There are two choices for the strong factor:

**Scaled choice:** S=i*Delta*c^2, Ns=Delta*f^2-S^2, and

    Q118=N0*N1*Na*Nt*Ns-Delta.

**Ordinary choice:** I=i*c^2, Ns=1+I^2-Aaux, and

    Q94=N0*N1*Na*Nt*Ns-1.

The two requested equations are respectively Q118=0 and Q94=0. They are
ordinary integer-coefficient polynomials. Each displayed exponent is a
fixed nonnegative integer. Divisions used below occur only in witness
reconstruction proofs, never in the equations or their evaluators.

The exact coefficients satisfy

    beta>=31, K0>0, 0<MC<beta<MF<2*beta.

They also satisfy the full native interface in the retained low-padding
proof: B=beta+1 is a power of two, MC=2 modulo4, MF-beta=4 modulo8,
the mask populations sum to47*2963, and the native masks/transition tuple
have the stated soundness and cofinal completeness calibration. A generic
four-tuple satisfying just the scalar boxes has no asserted ZFC meaning.

## 2. Elementary first-Pell facts

For m>=2, the equation x^2-m(m+1)u^2=-1 has no integer solution.
Indeed take a solution with least positive |u|, replacing x,u by their
absolute values. Squaring gives m*u<x<(m+1/2)*u. Multiplication by the
inverse norm-one unit (2m+1)-2*sqrt(m(m+1)) gives a new integral solution
whose second coordinate is u'=(2m+1)u-2x, strictly between0 andu.
Taking the absolute value of its first coordinate contradicts minimality.

Every positive solution of x^2-m(m+1)u^2=1 is a positive power of the
unit (2m+1)+2*sqrt(m(m+1)). The least positive ordinate is2: ordinate1
would put m^2+m+1 strictly between consecutive squares. Multiplication
by the inverse of the least unit gives the elementary descent/classification.
Consequently, for P=2m+1,

    x=chi_P(r), u=2*psi_P(r), r>=1,

where chi_P and psi_P are the standard Pell sequences. If E dividesm,
the recurrence chi_0=1,chi_1=P,chi_(r+1)=2P*chi_r-chi_(r-1) gives
x=1 moduloE. Also u=2 at r=1, while u>=4P at r>=2, and x>u.

These statements concern ordinary finite integer recurrences and descent;
they are formalizable in ZFC.

## 3. Unit signs are determined before using the carrier

At every positive assignment,

    Delta=(a+2)^2-1>0, Delta=0 or3 modulo4,
    ell*(ell+k)=m(m+1)k^2, m=EY>=2.

For Q118=0, write

    Ns=Delta*Nbar, Nbar=f^2-Delta*i^2*c^4.

Cancel the nonzero integer Delta in the mathematical equality. The
integral factors N0,N1,Na,Nt,Nbar multiply to1 and hence are units.
The mod-four square table excludes Nbar=-1, so Nbar=1, Ns=Delta and

    Aaux=Delta*(f^2-1)=S^2.

The first-Pell obstruction excludes N0=-1. The same mod-four square
table excludes N1=-1. Because Aaux is now a square, Na is congruent to
y^2 or V^2 modulo4, excluding Na=-1. There is only one remaining
unit factor. Therefore

    N0=N1=Na=Nt=1, Ns=Delta.                (scaled case)

For Q94=0, all five factors are units directly. If I^2,f^2 are reduced
modulo4 to0 or1 and Delta to0 or3, then

    Ns=1+I^2-Delta*(f^2-1)

has residue0,1 or2, never3. Thus Ns=1 and I^2=Aaux. The other norm
signs follow exactly as above, giving

    N0=N1=Na=Nt=Ns=1, I^2=Aaux.           (ordinary case)

No sign of C,V or the derived tau has been assumed in this step.

## 4. Scalar rank bounds and exact restoration of h

If C<=0, then K0+w>0, F,z>=1 imply

    Nt=(K0+w)*C+(q-F)-z*(q-1)<=0,

contradicting Nt=1. Hence C>0. Put u=q-F=C+alpha. Then
2<=u<=q-1 and1<=alpha<=u-1. For G=(q-1)u+alpha,

    2q-1<=G<=q^2-q-1,
    0<(MC+q*MF)*J<(1+2q)*(q-1).

Substituting in the exact R formula gives

    q*(q^2-1)<R<q^4-q^3<q^4-2,
    E=ws*q^4>=q^4>R+2.

In particular R>1 and tau=E*n+k-R>k+2>0. Applying Section2 to N0=1
with m=EY gives tau=1 moduloE. Hence

    h=(k-R-1)/E

is an integer. Since R+1<E and k>0, h>-1, so h>=0. If h=0,
k=R+1<E. The first Pell index r=1 would give k=2 and R=1; any r>=2
gives k>=4(2EY+1)>E. Both are impossible. Thus h>0 and

    Nk:=k-hE-R=1.

This restores exactly the index factor omitted by the new equations.
The argument is independent of which strong factor was used.

Conversely, any canonical positive parent solution with Nk=1 has
tau=1 moduloE and tau>k. Thus

    n=(tau-k+R)/E

is a positive integer and its carrier expression recovers the original
tau. These maps are asserted on the relevant zero/canonical sets, not
as bijections between ambient positive coordinate spaces.

## 5. Scaled equation: exact same positive zero set as Carrier65

Define P150 to be the same fourteen-variable expression as Q118 except
that its auxiliary factor is

    Na_old=S^2*(V^2-y^2)+y^2.

This is precisely the first-Pell carrier polynomial of the incoming
Carrier65 archive, applied uniformly to the complete current coefficient
tuple. That archive's original numerical tuple was admissible942; we do
not equate those different tuples. The retained block-mask2963 theorem
supplies the full P66 calibration at the new tuple, and the carrier proof
uses only its already established scalar boxes and canonical witnesses.

There is an exact identity over the full polynomial ring:

    Q118-P150=N0*N1*Nt*Ns*(Ns-Delta)*(V^2-y^2).

At a positive zero of either polynomial the normalized strong unit is1,
so Ns=Delta. Thus the other polynomial vanishes at the identical tuple.
This is an exact equality of positive zero sets, not merely an existence
reduction. By Section4, P150 restores the P66 index factor and root; its
reverse map uses canonical P66 witnesses. Composing with the full pinned
block-mask native/Pell/refutation theorem proves

    ZFC proves: (Q118 has no positive integer zero) iff Con(ZFC).

## 6. Ordinary equation: relaxed strong norm with a restored carrier

At a positive Q94 zero, Sections3-4 restore positive h and tau and give
N0=N1=Na=Nk=Nt=1 and I^2=Delta*(f^2-1), I=i*c^2.
These are precisely the ordinary-strong product conditions of the
source59 p68_d101 polynomial, whose entire literal parent circuit is
retained. Its quotient V=f^2*(cT-R)-c is the squared-modulus version of
the relaxed-rank source53 quotient:

    c*((f*T)*f-1)-R*f^2=f^2*(c*T-R)-c.

Thus T_old=f*T is a strictly positive exact pullback. The complete
relaxed-rank proof is retained in
`sources/53-selective-quad_short_PROOF.md`; the precise Pell dependency
audit is also retained. The key mathematical distinction is that one may
not silently divide an arbitrary ordinary i by Delta.

For clarity, here is the arithmetic path of that proof at our stronger
positive-sign interface. Put A=a+2, P0=2EY+1. Main-Pell classification gives
c=psi_A(p),D=chi_A(p); first-Pell classification gives k=2psi_P0(r).
The index congruence implies 2r=R+1+bE, b>=0, so r is large. P0>A and
c>k imply p>r. Standard Pell growth then gives

    c>A*Delta^2, c>2p, c>2R.

The retained relaxed-rank lemma proves that I^2=Delta*(f^2-1), I=i*c^2,
with this size condition implies, for an integer m>0,

    f=chi_A(m), p|m, c|m, I=Delta*psi_A(m).       (1)

Its proof factors Delta=d*s^2 with d squarefree, expresses A and f as
powers of the least positive integral unit in Q(sqrt(d)), and applies
the strong divisibility identity for psi to the two indices. If their
gcd is a proper divisor of the main index, doubling bounds force
psi(g)^2<Ac/2 while c>A*Delta^2 gives psi(g)^2>Ac. The remaining
composition and the binomial expansion at the p-th Pell unit imply
p|m and c|m. This full descent/divisibility argument, including the
nonsquarefree Delta case, is reproduced in the retained source53 proof.

Equation(1) gives c^2|f^2-1, f>2c and m>=c>2p. With rho=I and R<a<Delta,

    rho^2>R*f^2+c.

The auxiliary norm rho^2*V^2-(rho^2-1)y^2=1 and T_old>0 then force V>0:
if |V|>1, its norm gives |V|>=2rho^2-1, incompatible with negative V;
V=0 and V=+1,-1 are excluded by the norm and V=-c modulof. The positive
integer auxiliary quotients are restored exactly as in source53.

The retained plus-congruence step-down theorem applies to the auxiliary
Pell index. Its hypotheses are f=chi_A(m), c|m, m>2p, c|rho,
rho^2=Delta*(f^2-1), V=-c modulof, V=-R moduloc and 0<R,p<c/2.
It yields R=+p or-p moduloc, whence p=R. The fixed-minus parity and
half-binomial/population arguments then recover the genuine native data
and refutation. Their exact interfaces and source references are in the
retained Pell audit, Sections4-5. Our transformation changes none of
their variables, inequalities, coefficient meanings or native masks.

This soundness route uses the complete authentic block-mask tuple. The
source53 proof explicitly states its uniform four-port native interface;
the low-padding proof supplies that same interface with the new whole
tuple. No coefficients from two instances are mixed.

For completeness, begin with the current normalized P66 canonical
witness supplied by a finite refutation. It has every ordinary factor1,
normalized strong equation f^2=1+Delta*i_old^2*c^4, and the squared-
modulus quotient. Replace only the strong multiplier by

    i_new=Delta*i_old.

Then (i_new*c^2)^2=Delta*(f^2-1); the auxiliary coefficient is the old
S^2, and Ns=1. Set n=(tau-k+R)/E as in Section4 and omit h,tau.
All new variables are positive and Q94=0. Combining both directions gives

    ZFC proves: (Q94 has no positive integer zero) iff Con(ZFC).

## 7. Exact operation counts and attained degrees

All additions, subtractions and multiplications, including squares and
fixed-integer multiplications, cost one binary operation. Integer leaves
are free; division and rational leaves are not used. Only the fourteen
listed positive inputs are unknowns. Every fixed port and producer is live.

The current P66 graph has66 rows. Deleting the three Nk producers and
one output multiplication, and adding the three carrier producers,
gives the already known65-row P150. Its scaled_f2=Delta*f^2 row is
already present. One subtraction forms Aaux=scaled_f2-Delta, so Q118
has66 rows. The older ordinary product graph has68 rows; the identical
carrier change gives67. The literal counts are37M+16A+13S and
37M+17A+13S respectively.

Let Q=beta*J and k0=eta+zeta. The shared factor degrees are

    degree(N0)=22, degree(N1)=18, degree(Na)=30, degree(Nt)=2.

The derived carrier tau has degree7, whose square cannot cancel the
degree22 first-product term. The main cancellation is exact, with
Z=X+gamma*H:

    N1=Z^2+2*a*c*Z-H*c^2.

The independent checker expands its entire323-term ancestor polynomial
before computing its degree18 leader; no false degree22 estimate is used.

The scaled Ns has degree46, giving total118. Its full highest homogeneous
form is

    8*Q^67*gamma*i^2*k0^9*w^10*s^19*T^2*f^6
       *(w*(Q-F-alpha)-z*Q).

Its coefficient at J^68*gamma*i^2*eta^9*w^10*s^19*T^2*f^6*z is
-8*beta^68, nonzero for the actual beta. Thus degree118 is attained.

The ordinary Ns has degree22, giving total94. Its full highest form is

    -8*Q^51*gamma*i^2*k0^9*w^6*s^15*T^2*f^6
       *(w*(Q-F-alpha)-z*Q).

Its coefficient at J^52*gamma*i^2*eta^9*w^6*s^15*T^2*f^6*z is
8*beta^52, again nonzero. Each full form contains40 monomials, all checked
symbolically by the independent verifier.

## 8. What is new here and what remains inherited

This packet fully emits and checks the two combinations with the latest
whole block-mask2963 tuple. It combines the incoming first-Pell carrier
with two older degree-reduction mechanisms. It does not claim invention
of any of those mechanisms, global optimality, or a literature-wide
priority result. Its primary value is a concrete cost/degree improvement:
14-positive66/118 and67/94, against the already delivered65/150 point and
the older14-positive70/189 and71/157 points.

The new exact transformations and their degree/count proofs are proved
above. The original calibrated P66 native/Pell theorem, its explicit
K215/refutation connection, and the retained relaxed-rank/step-down
theorems are inherited dependencies identified in the source ledger.
The packaged finite controller certificate is retained from the accepted
current tuple. No new native or formal-kernel replay is claimed.
No statement here proves consistency or actual unsolvability.
