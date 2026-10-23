# Regrouping the relaxed-rank kernel: 72 operations, degree 80

## Scope and prior art

The new result in this directory is a tradeoff: one polynomial in fifteen
strictly positive integer unknowns, exact degree 80, and 72 charged binary
arithmetic operations. It saves one multiplication against the pinned
degree-80 P73 evaluator, but is not a global operation-count record. The
67-operation, degree-155 polynomial remains smaller by that metric.

The relaxed auxiliary norm is NOT new. Historical package 10 already uses
it in Q56 (degree 56, 74 operations); its literal JSON is in history/.
Our P74 has exactly that degree/operation pair and is only an alternate
grouping. Historical degree/operation pairs 99/69, 93/70, 83/71, 56/74 and
44/78 must also be retained in comparisons. The claimed contribution is
the 80/72 point and an explicit proof/audit of its assembly, not invention
of the relaxed rank theorem or a claim of major theoretical breakthrough.

The arithmetic source is pinned to ProveIt commit
124c07c0b77a9e20e84676514d8b1ff78536ea3f. The mathematical proof below is
formalizable in ZFC and uses the inherited calibrated blank-K215 compiler.
It is not a new end-to-end Lean certificate. In particular the Lean
same-coordinate equivalence theorem for normalized P75 does not apply to
this changed norm. No claim that ZFC is consistent is made.

## 1. Explicit fixed polynomial

The positive witnesses are

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

Use the WHOLE four-port tuple in COEFFICIENT_BINDING.json: beta=B-1,
K0=K, MC=MC, MF=MF_source, where B=2^1064921 and MF_source is shifted.
Every gzip payload contains an unsigned little-endian integer. All hashes
and byte lengths are provided. No port comes from the smaller wave6 tuple.

The following are polynomial abbreviations, not extra unknowns:

    q=beta*J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, A=a+2,
    H=4a+3, Delta=a^2+H=A^2-1, D=X+ac+gamma*H,
    G=(q-1)(q-F)+alpha,
    R=G(q^2-1)+(MC+q*MF)J,
    V=c(Tf-1)-Rf^2, I=ic^2, Kaux=Delta(f^2-1).

Set

    N0=tau^2-(XY^2)(XY^2+1)k^2,
    N1=D^2-Delta*c^2,
    Na=Kaux(V^2-y^2)+y^2,
    Nk=k-hE-R,
    Nt=(K0+w)C+(q-F)-z(q-1),
    S=I^2-Kaux.

The main equation is

    P72=(N0*N1-1)^2+(Na*Nk*Nt-1)^2+S^2=0.       (1)

The companion equation is

    P74=(N0-1)^2+(Na-1)^2+S^2+(N1*Nk*Nt-1)^2=0. (2)

The two source JSON files are literal division-free evaluators for these
ordinary integer polynomials. All powers have fixed nonnegative exponents.

## 2. Sign classification and preliminary bounds

At a zero of (1), S=0, so Kaux=I^2 is a positive integer square; every
factor N0,N1,Na,Nk,Nt is an integer unit. The consecutive-product negative
Pell descent excludes N0=-1. Since Delta=(a+2)^2-1 is 0 or 3 modulo 4,
N1 cannot be -1. Since Kaux is a square, Na is congruent modulo 4 to either
y^2 or V^2 and cannot be -1. Thus

    N0=N1=Na=1, Nk=epsilon, Nt=nu,
    epsilon,nu in {-1,1}, epsilon*nu=1.           (3)

The same conclusion follows from (2): its grouped factor makes N1 a unit,
and the modulo-four argument fixes its sign. Conversely (3) together with
S=0 implies both equations. This step does NOT assume either remaining
sign positive.

For clarity, the negative-Pell descent used here is elementary: for
v>1, a positive solution of x^2-v(v+1)z^2=-1 with least z satisfies
vz<x<(v+1/2)z. Multiplication by the inverse unit
2v+1-2sqrt(v(v+1)) gives a new positive coefficient
(2v+1)z-2x strictly between 0 and z, a contradiction.

The fixed tuple satisfies B>=16, K0>0, 0<MC,MF_native<B-1,
MF=MF_native+B-1. Weak transport in (3) implies C>=0, not yet C>0:
if C<=-1 then Nt<=-(K0+w)<=-2. Thus q-F=C+alpha>0, and the exact
preliminary bounds from direct substitution are

    q<=G<=q^2-q,
    q(q^2-1)<R<q^4-q^3+q^2-1<q^4-2,
    R-2>3q+1, E>=q^4>R+2, a>R+2.

Indeed the mask term is between 0 and (q-1)(1+2q). These estimates do
not use coefficient decoding, an auxiliary rank, or the excluded C=0
boundary.

Put P0=2XY^2+1. The first norm and main norm classify as

    tau=chi_P0(n), k=2psi_P0(n),
    D=chi_A(p), c=psi_A(p), n,p>=1.

For the first classification, the least positive coefficient in
x^2-v(v+1)z^2=1 is 2, with root 2v+1: coefficient 1 lies between
consecutive squares. P0=1 modulo E implies

    2n=R+epsilon+bE, b>=0, n>=(R-1)/2>=24.

Because P0>A and c>k, monotonicity gives p>n. The Pell growth bound
psi_A(p)>=(2A-1)^(p-1) yields c>A*Delta^2 and c>2p. Also
k=R+epsilon+hE>2R gives c>2R. All these facts precede the relaxed
auxiliary argument.

## 3. Relaxed rank lemma, with proof

We need the precise statement: if A>=2, Delta=A^2-1,
c=psi_A(p)>A*Delta^2, and (ic^2)^2=Delta(f^2-1) with i,f>0,
then for some m>0,

    f=chi_A(m), p|m, c|m, ic^2=Delta*psi_A(m).    (4)

No claim c^2|psi_A(m) is part of this lemma.

Write Delta=d0*s0^2, d0>1 squarefree. Choose the least positive
integer-coefficient norm-one unit F+y0 sqrt(d0). Division by powers of
this least unit proves that every positive integer-coefficient norm-one
unit is its power. Consequently, for some e>=1,

    A=chi_F(e), s0=y0*S0, S0=psi_F(e),
    Delta=(F^2-1)S0^2, psi_F(ep)=S0*c.

The relaxed equation forces s0|ic^2 and d0|(ic^2/s0). Hence it gives
another integral unit f+y sqrt(d0), with y=ic^2/(d0*s0)>0. For some t>0,

    f=chi_F(t), ic^2=(F^2-1)S0*psi_F(t).

Let L=(F^2-1)S0<=Delta and g=gcd(t,ep). Strong divisibility of the
Pell sequence (proved by its addition identity and Euclid's algorithm)
gives gcd(psi_F(t),psi_F(ep))=psi_F(g). Since c^2 divides L*psi_F(t),

    c*gcd(c,Delta)
      =gcd(c^2,L*psi_F(ep)) divides L*psi_F(g).

Thus psi_F(g)>=c/Delta. If g<ep, then 2g<=ep, and doubling yields

    2psi_F(g)^2<psi_F(2g)<=psi_F(ep)=S0*c<A*c.

But c>A*Delta^2 implies psi_F(g)^2>=c^2/Delta^2>A*c, contradiction.
Therefore ep|t. Write t=e*m; then p|m, and composition yields
f=chi_A(m), ic^2=Delta*psi_A(m).

Write m=p*b. The binomial expansion of (D+c sqrt(Delta))^b gives
psi_A(pb)/c=b D^(b-1) modulo c. Since c^2 divides Delta*psi_A(m)
and gcd(D,c)=1, we get c|Delta*b. Meanwhile
c=psi_A(p)=p A^(p-1) modulo Delta, so
g0=gcd(c,Delta)=gcd(p,Delta) divides p. It follows that c/g0 divides b,
and hence c divides pb=m. This proves (4).

## 4. Deleted quotient witnesses remain legitimate

The crucial order change is to use (4) BEFORE restoring the auxiliary
quotients. Put rho=ic^2. Since p|m, psi_A(m) is a positive multiple
of c. Therefore

    c^2 | f^2-1,
    f^2>=1+Delta*c^2, f>2c,
    rho^2=Delta(f^2-1), c|rho,
    m>=c>2p.

Since R<a<Delta,

    rho^2-(Rf^2+c)
      =(Delta-R)f^2-Delta-c
      >=f^2-Delta-c>0.

The auxiliary norm is rho^2 V^2-(rho^2-1)y^2=1. It excludes V=0.
If v=|V|>1, then v^2-1=(rho^2-1)(y^2-v^2) implies y>=v+1,
and therefore v>=2rho^2-1. On the other hand T>0 implies
V>-(Rf^2+c)>-rho^2, excluding all such negative V. The values
V=1 and V=-1 contradict V=-c modulo f, since c>2 and f>2c.
Thus V>0.

The proof-only restored quantities

    o=cT-Rf,
    j=Tf-R(f^2-1)/c-1

are INTEGERS, since c divides f^2-1. They obey

    of=V+c>0, jc=V+R>0, V=of-c=jc-R.

So o,j are positive. These divisions occur only in the proof, not in
the emitted polynomial. The normalized formula
j=Tf-R*Delta*i^2*c^3-1 must NOT be used with the new i.

## 5. Main target, sign recovery, and inherited compiler

The inherited auxiliary step-down now applies with exactly its stated
hypotheses: f=chi_A(m), c|m, m>2p, rho>1, c|rho,
rho^2=Delta(f^2-1), V,y>0, V=-c modulo f, V=-R modulo c,
and 0<R,p<c/2. Here is its key reduction, to make the dependency explicit.
The auxiliary norm gives rho V=chi_rho(ell), y=psi_rho(ell), with ell
odd. Write ell=2u+1 and chi_Z(ell)=Z Q_u(Z^2). The identities

    Q_u(1-A^2)=(-1)^u psi_A(ell), Q_u(0)=(-1)^u ell

give (-1)^u psi_A(ell)=-c modulo f and
(-1)^u ell=-R modulo c. Squaring the first gives
chi_A(2ell)=chi_A(2p) modulo chi_A(m). The retained plus-congruence
step-down theorem yields ell=+p or -p modulo m, hence modulo c.
Thus R=+p or -p modulo c, and the strict half-interval bounds give p=R.
The precise statement and source of that elementary step-down theorem
are in upstream_verified/INHERITED_PELL_AUDIT.md, Section 4.

Return to 2n=R+epsilon+bE. If b>=1 then 2n>=R-1+E>2R, contrary
to n<p=R. Thus b=0. If epsilon=-1 then p=2n+1. Put
Q=chi_A(2)>P0; since A>Y+1, duplication and parameter monotonicity give

    c=psi_A(2n+1)>psi_A(2n)
      =2A psi_Q(n)>=2A psi_P0(n)=A*k>k(Y+1),

contradicting kY<c<k(Y+1). Hence epsilon=nu=1 and C>0.

All hypotheses of the inherited fixed-minus parity theorem are now met,
so R=p=3 modulo 4. The lower-ratio argument, half-binomial theorem,
inverse-population lemma and native decoder then apply unchanged, as
listed in Sections 4--5 of INHERITED_PELL_AUDIT.md. In particular they
use (4), not the stronger c^2|psi_A(m). They recover X=2^R, q=B^N,
the repeated masks and the calibrated finite blank-K215 computation.

One can alternatively return to the normalized parent explicitly. After
p=R=3 modulo 4, replace only the auxiliary witnesses by the canonical
ones m'=2cR, f'=chi_A(m'), i'=psi_A(m')/c^2,
rho'=Delta*psi_A(m'), y'=psi_rho'(R), V'=chi_rho'(R)/rho'.
The binomial expansion proves c^2|psi_A(2cR). The odd quotient identities
give V'=-c modulo f' and V'=-R modulo c. Thus
o'=(V'+c)/f' and T'=(o'+Rf')/c are positive integers; the latter
integrality uses f'^2=1 modulo c. They satisfy the normalized strong
norm and the same outer kernel. This is a witness replacement, not a
same-coordinate identity.

## 6. Completeness

The inherited normalized parent supplies a positive solution from a
finite ZFC refutation, using this entire fixed tuple. Leave every outer
witness and f,T,y unchanged, and replace i_old by

    i_new=Delta*i_old.

Then (i_new*c^2)^2=Delta^2(i_old*c^2)^2=Delta(f^2-1).
Kaux and V remain unchanged. All five norm/index/transport factors
are +1, so (1) and (2) vanish. This proves both directions and hence

    ZFC proves: (no positive solution of P72=0) iff Con(ZFC).

The same statement holds for P74 and the six-equation system.

## 7. Complete coefficient adapter, not a mix of ports

The delivered tuple is the 121-by-8801 Wang943 tuple, not the smaller
complement-packed wave6 tuple used in the exploratory draft. Its complete
finite recipe, literal language, support geometry, carry bound, mask
population proof, and actual-rank controller are reproduced in
upstream_verified/COEFFICIENT_PROOF.md. The original binding is retained
in coefficients/original_binding.json. The exact adapter interface is:

* beta=2^1064921-1 and q=beta J+1;
* K0=DC+B*DR, with the current and temporal native products fixed by that
  recipe; MC is the native low mask and MF is MF_native+B-1;
* 0<MC,MF_native<B-1, MC=2 modulo 4, MF_native=4 modulo 8, and the
  two native mask populations sum to 1064921;
* the low mask produces Boolean supported copies, the clause and overlap
  masks encode the literal 943-tile blank-K215 language, and the two clean
  bands plus anchors force whole-cell temporal alignment;
* completeness pads a genuine halting tableau and adjusts only ignored
  dummy bits so its actual packed R has the required temporal residue,
  while preserving positive slack, all masks, R=3 modulo 4, and the
  exact population identity needed by the Pell converse.

These are exactly the hypotheses used above and by the normalized parent.
No algebraic step depends on an old value of the inner radix or cell width.
The adapter proof supplies this interface for the complete selected tuple,
so replacing all four ports together is legitimate. The finite auditor
independently checks the actual payload bytes, ranges, congruences and
population balance. It does not replace the native semantic proof.

## 8. Exact arithmetic audit

The prefix has 61 live producers (34 multiplications, 27 additions or
subtractions). P72 adds three group products, three residual subtractions,
three squares and two additions: 72=40M+32A. Its residual degrees are
40,37,22. P74 adds two products, four subtractions, four squares and
three additions: 74=40M+34A, with degrees 22,28,22,27.

The exact degree-18 main norm follows from the identity, with Z=X+gamma H,

    D^2-Delta c^2 = 2acZ+Z^2-Hc^2.

The auditor expands this initial cone exactly in the integer polynomial
ring before propagating nonzero leading homogeneous forms. P72's leader is

    64 gamma^2 w^8 s^14 (eta+zeta)^6 (beta J)^50,

and P74's leader is

    w^4 s^8 T^4 f^8 (eta+zeta)^4 (beta J)^28.

Their displayed monomials have nonzero coefficients 64 beta^50 and
beta^28. This proves exact degrees 80 and 56 for the actual tuple,
without substituting identities that hold only at solutions. The system
has six residual degrees 22,18,28,7,2,22 and 61 charged operations,
with equality comparisons uncharged under the repository convention.

Run build_relaxed.py, then audit_relaxed.py (also under python -O).
The auditor checks literal inherited producers, input and gate liveness,
exact degrees and leading forms, four complete coefficient payloads,
source git blob identities, and the grouped unit-sign truth table.
These finite checks complement the proof; they are not a test of Con(ZFC).

