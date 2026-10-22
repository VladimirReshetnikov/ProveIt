# Smaller arithmetic schedules at degrees 44, 50, 70 and 80

These packets combine ordinary strong norms, positive first/auxiliary gaps,
and grouped unit equations. They do not beat the 67-operation polynomial,
the 13-positive-variable construction, or the 32-variable quartic. Their
improvement is a genuine operation/degree tradeoff at fixed 15 positive
variables. No global minimality claim is made.

The literal single-polynomial DAGs are:

* grouped_doublegap76_degree44.json: 76 operations, degree 44.
* grouped_auxgap75_degree50.json: 75 operations, degree 50.
* grouped_firstgap73_degree70.json: 73 operations, degree 70.
* grouped_ordinary72_degree80.json: 72 operations, degree 80.

Each operation is one binary addition, subtraction or multiplication.
Squaring and multiplication by fixed coefficients count. Reuse is free.
The four compiler ports are fixed integers, not extra variables. A single
coherent authentic Start-only blank compiler tuple must be selected.
These transformations do not authorize mixing coefficient packages.

## 1. Common notation and the literal polynomial

Write the fifteen ordinary positive coordinates as

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

Here z is the OLD positive transport quotient. It is not the shifted z
used by package12's system60. Put

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H, D=X+ac+gamma H,
    L0=EkY, C=q-F-alpha,
    G=(q-1)(q-F)+alpha,
    R=G(q^2-1)+(MC+q MF)J,
    V=c(Tf-1)-Rf^2, I=ic^2, U=Delta(f^2-1).

The five unit expressions and the ordinary strong residual are

    N0=tau^2-L0(L0+k),
    N1=D^2-Delta c^2,
    Na=U(V^2-y^2)+y^2,
    Nk=k-hE-R,
    Nt=(K+w)C+q-F-z(q-1),
    S=I^2-U.

An optional first gap replaces tau by L0+t; an optional auxiliary gap
replaces y by V+e. The new coordinates t,e are positive. The exact
polynomial identities are

    N0=t^2+L0(2t-k),
    Na=(V+e)^2-U e(2V+e).

The DAG uses the shared-square evaluations rather than naively expanding
these identities. Each gap costs just one added addition.

The four new polynomials are, with the stated gaps applied:

    Q44=(N0 Nk-1)^2+(N1 Nt-1)^2+(Na-1)^2+S^2.
    Q50=(N0 Nt-1)^2+(N1 Nk-1)^2+(Na-1)^2+S^2.
    Q70=(N0 N1 Nt-1)^2+(Na Nk-1)^2+S^2.
    Q80=(N0 N1-1)^2+(Na Nk Nt-1)^2+S^2.

Q44 uses both gaps, Q50 only the auxiliary gap, Q70 only the first gap,
and Q80 neither. These are definitions of literal polynomials, not
quantifier-bearing shorthand: each JSON contains every binary gate.

## 2. Soundness, completeness, and signs

A sum of integer squares is zero exactly when every listed residual is
zero. Thus each of N0,N1,Na,Nk,Nt is an integer unit, their product is 1,
and S=0. With Ns=1+S, the ordinary product

    N0 N1 Na Nk Nt Ns-1

therefore vanishes after restoring the optional roots. This is the
ordinary69 polynomial, not merely an analogy with it.

For Q44,Q50,Q70 one may recover individual units directly. N1 cannot be
-1 modulo 4 because Delta is 0 or 3 modulo 4. U is 0 or 1 modulo 4,
so Na reduces to y^2 or V^2 modulo 4 and cannot be -1. N0 cannot be -1
by the standard negative-Pell descent for n(n+1), here n=XY^2>1. In each
of these three groupings Nk and Nt are in separate groups, each with
only already-positive norm units; hence Nk=Nt=1. For Q80 they are in the
same group: its soundness uses the full ordinary product unit-sign
recovery in package12 ORDINARY_BLANK_PROOF.md, Sections 3-7. Treating its
two linear units as automatically positive would be an error.

Restored tau=L0+t is positive. Restored y=V+e need not be positive off
the zero set. There are two valid ways to finish soundness. The signed-y
theorem in package12 permits this coordinate to be an arbitrary integer.
Alternatively, S=0 gives U=I^2>1 and Na=1 excludes y=0; replacing restored
y by its positive absolute value leaves every source equality unchanged.
This supplies a positive old source solution and hence an accepting
blank computation. No sign assumption on a computed V was used to
justify this restoration.

For completeness use the established canonical positive ordinary
compiler witnesses. They have V>1 and U>1, and therefore

    tau^2-L0^2=L0 k+1>0,
    (U-1)(y^2-V^2)=V^2-1>0.

Thus t=tau-L0 and e=y-V are positive. All five unit expressions equal 1
and S=0, so each required grouped polynomial vanishes. This establishes
equivalence of existence of positive solutions. No unnecessary claim
about a bijection of every original positive tuple is required.

The inherited compiler and K215 blank-halting/refutation calibration now
give: each displayed polynomial has no positive solution iff Con(ZFC).
Replacing each variable v by n_v+1 gives the same statement over
nonnegative integers, with the same variable count and degree. This is
an ordinary mathematical reduction with inherited Pell/compiler
dependencies, not a new end-to-end proof-assistant verification.

## 3. Literal operation ledger

The ordinary source computes the five unit expressions and both sides
of S=0 using 61 operations. The first/auxiliary gaps add one each.
Partition the five units into r groups. Multiplying within groups costs
5-r gates; subtracting one for each group and forming S costs r+1;
squaring costs r+1; summing costs r. The additional total is 7+2r.

Consequently Q80 costs 61+11=72, Q70 costs 62+11=73, Q50 costs
62+13=75, and Q44 costs 63+13=76. The emitted DAG ledgers independently
give 40 multiplications in each, with respectively 32,33,35,36 additions
or subtractions. All fifteen inputs, four fixed ports, and gates are live.

## 4. Exact degrees for every authentic coefficient tuple

Let Q=beta J, the highest homogeneous part of q. Then X,Y,E,c,a have
degrees 2,4,6,5,6, with nonzero leading forms

    wQ, sQ^3, wsQ^4, ksQ^3, wsQ^4.

Their displayed coefficients are nonzero for every beta>0. The leading
forms of the unsheared/specialized factors follow directly:

* N0 without the first gap: -L0^2, degree 22.
* N0 with the first gap: L0(2t-k), degree 12.
* N1: 8 gamma a^2 c, degree 18, using
  D^2-Delta c^2=2ac(X+gamma H)+(X+gamma H)^2-Hc^2.
* Na without the auxiliary gap: a^2 c^2 T^2 f^4, degree 28.
* Na with the auxiliary gap: -2 a^2 c T f^3 e, degree 22.
* Nk: -hE, degree 7.
* Nt: w(Q-F-alpha)-zQ, degree 2.
* S: i^2 c^4, degree 22.

In this list each expression on the right denotes its highest homogeneous
part, using the leading a,c,E,L0 just described. Products of nonzero
polynomials over the real numbers do not vanish. Subtracting 1 does not
affect positive degrees. The residual degrees are therefore exactly

    Q44: 19,20,22,22;
    Q50: 24,25,22,22;
    Q70: 32,35,22;
    Q80: 40,37,22.

The leading part of a real sum of squares cannot vanish unless every
leading summand does. Hence the total degrees are exactly 44,50,70,80,
uniformly for every admissible compiler tuple, not merely at a numerical
test specialization.

## 5. Audit and negative search scope

build_grouped_tradeoffs.py is newly authored. It reads literal parent
JSON, checks DAG closure, full liveness and arithmetic ledgers, and
compares 100 complete signed integer evaluations per packet with
independently written formulas. No received Python source is imported or
executed. The bounded checks do not decide any polynomial's solvability.

The separately owned search_elimination.py explored direct polynomial
register elimination from package12's quartic32, with beam width 100,
with and without first/main positive-root shears. It found no improvement
over 25 variables for cubic residuals or 21 for quartic residuals in that
two-auxiliary-quotient representation. Those are search observations,
not lower bounds; the previous merged-quotient degree-eight construction
already uses 20 variables. No <67-operation or <32-variable quartic
construction was established in this search.
