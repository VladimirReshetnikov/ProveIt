# Quotient fusion in the signed native system

This is a composition of inherited mechanisms with new literal endpoints,
not a claim that the CRT quotient or square-modulus lemma is new.

## Measured results

The standard-library builder and exact homogeneous-coefficient verifier give:

| Polynomial | Domain | Variables | Degree | Rows | Live binary operations |
|---|---|---:|---:|---:|---:|
| quotient20 | unrestricted integers | 20 | 24 | 8 | 120 |
| quotient19 | unrestricted integers | 19 | 32 | 7 | 116 |
| quotient18 | unrestricted integers | 18 | 88 | 6 | 114 |
| quotient20_transport | unrestricted integers | 19 | 28 | 7 | 116 |
| quotient19_transport | unrestricted integers | 18 | 32 | 6 | 112 |
| quotient18_transport | unrestricted integers | 17 | 88 | 5 | 110 |

The 20-variable source comparison is the incoming Joint_Guards 20/32
endpoint. Its 19-variable endpoint is degree 88. The new 18/88 endpoint
has one fewer unrestricted variable at that degree. These changes do not
beat the existing ten-integer bound at very high degree. A degree/circuit
tradeoff is explicit: these operation counts are not claimed to be minima.

The last three rows apply the exact transport parametrization in Section 7.
The resulting nondominated variable/degree points from this component are
20/24, 19/28, 18/32, and 17/88; the two dominated CRT checkpoints remain
for transparent algebraic comparison.

## 1. Fixed tuple and polynomial abbreviations

Use the complete source34 native tuple, including its already-shifted MF,
and the two source71 determinant scales:

    beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104.

K0, MC, MF retain their complete authentic source34 numeral definitions.
For the integer inputs set

    J=3J3+1, q=beta*J+1, W=4(3w3+1), X=qW,
    Y=(2v+1)q^3, C=q-F-alpha,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    H=4a+3, Delta=a^2+H,
    k=R+1+hE, zeta=k-eta,
    I=(2r+1)c^2, Q=Delta(f^2-1),
    B=f^2(cT-R), V=B-c,
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Z=eta*zeta, Pos=1+p1^2+p2^2+p3(p3+1).

The 20-variable equation keeps a and c as inputs and defines E=a-Y.
Its inputs are J3,F,alpha,z,f,h,r,v,w3,tau,eta,y,gamma,T,a,c,t,p1,p2,p3.
The 19-variable equation instead defines E=XY,a=E+Y and drops a.
The 18-variable equation additionally defines eta=c-Yk and drops eta.
All other displayed letters are polynomial abbreviations, never unknowns.

Use these residuals where indicated:

    scale      = a-(X+1)Y                      [20 only]
    remainder  = c-eta-Yk                     [20 and 19 only]
    first      = tau^2+(2tau-k)E(c-eta)-1
    main       = (X+ac+gamma H)^2-Delta c^2-1
    transport  = (K0+W)C-F-z(q-1)
    strong     = I^2-Q
    auxiliary  = (B+y)^2-L(c+y)(2B+y-c)-1
    joint      = GZ-(t^2-G-Z+1)^2-Pos.

Here L=Q for the 20-variable equation and L=I^2 for the other two.
The single polynomial is the sum of the squares of the listed residuals.
Every displayed exponent is a fixed natural number.

## 2. Exact algebraic changes

The incoming source has two exposed quotient equations

    V+c=fo, V+R=cj.

Replace these by the polynomial definition V=f^2(cT-R)-c. This is an
existence-preserving restriction, with soundness and completeness below.
It removes o,j,V and introduces T, saving two coordinates.

The two integral shears are

    tau_old=E(c-eta)+tau, y_old=B+y.

The first identity is

    tau_old^2-E(c-eta)[k+E(c-eta)]-1
      =tau^2+(2tau-k)E(c-eta)-1.

The second uses

    y_old^2-V^2=(c+y)(2B+y-c).

The strong row permits replacing I^2 by Q in the auxiliary norm:

    A_new=A_old+(I^2-Q)(y_old^2-V^2).

This row operation is reversible on the zero set. Only the 20-variable
endpoint uses it: after substituting a=(X+1)Y, Q acquires higher degree,
so retaining I^2 produces better degrees in the smaller endpoints.

For 20 variables the scale row and E=a-Y imply E=XY and a=(X+1)Y.
For 19 and 18 these identities hold by definition. The remainder relation
likewise holds as a row or by definition. Thus the entire inherited kernel
outside the two removed quotients is exactly restored.

## 3. Soundness: derive divisibility before restoring the quotients

The generic nearest-square pair-positivity lemma (source68 and incoming
Joint_Guards) says that the joint row has some t,p1,p2,p3 exactly when
G>0 and Z>0. The source71 determinant lemma then restores common strict
signs of q,F,alpha,C. In particular, the authentic native coefficient
inequalities imply, with Q0=|q|,

    Q0>=16, Q0(Q0^2-1)<R<Q0^4-2.

The residue-oriented source has W=12w3+4, so W never vanishes and
|W|>=4. Together with Y=(2v+1)q^3 this gives

    |X|>=4Q0, |Y|>=Q0^3, |E|>=4Q0^4>3R+1.

The proof in incoming Joint_Guards/guards/PROOF.md, Section 4 through
"Pell classification and rank bootstrap", applies before any quotient
equation is used. For clarity, its order is reproduced here. Since
eta*zeta>0 and c=Yk+eta, c0=|c|>|k|>0. Put A0=|a+2| and
P0=|2XY^2+1|. The first and main Pell norms give positive indices n,p with

    |k|=2 psi_P0(n), c0=psi_A0(p), p>n.

The index identity k=R+1+hE gives either n>=(R+1)/2 or n>R. Thus p>n>=24.
Pell growth supplies c0>A0(A0^2-1)^2, c0>2p and c0>2R. The ordinary
strong-rank lemma, applied to I^2=Delta(f^2-1), now gives

    |f|=chi_A0(m), p|m, c0|m, m>2p.

None of these steps needs o,j, the auxiliary norm, or an auxiliary-rank
conclusion. This fact prevents circular restoration.

Since p|m, the elementary Pell divisibility identity gives
c0=psi_A0(p) dividing psi_A0(m). Therefore

    f^2-1=Delta*psi_A0(m)^2

is divisible by c^2. In particular it is divisible by c. This is not
obtained by dividing the ordinary strong equation by Delta: that shortcut
would be invalid without a coprimality proof.

We may now restore integers

    o=f(cT-R),
    j=(V+R)/c=f^2 T-1-R(f^2-1)/c.

They satisfy V+c=fo and V+R=cj literally. Restore y_old and tau_old by
the integral shears above. The full incoming signed kernel is recovered,
so its already proved signed auxiliary step-down, residue orientation,
native compiler and finite-refutation soundness apply. In particular an
integer zero of any new polynomial supplies a finite syntactic ZFC
refutation, relative to those explicitly inherited ordinary proofs.

## 4. Completeness: a fresh auxiliary Pell witness

The authentic canonical witnesses have R=3 modulo 4, a even,
A=a+2>1, c=psi_A(R)>0 odd, and Delta=A^2-1 odd. Choose the usual
ordinary strong witness

    m=cR, f=chi_A(m), i=Delta*psi_A(m)/c^2.

The binomial Pell expansion proves c^2 divides psi_A(cR), and its
quotient is odd. Hence i is an odd positive integer and i=2r+1 for an
integer r. Set S=i c^2=Delta*psi_A(m). Then

    S^2=Delta(f^2-1), c|S, f^2=1 modulo c.

Use the inherited source51 squared-modulus lemma, whose polynomial proof
only needs these displayed relations, rather than the name of the strong
multiplier:

    V=chi_S(R)/S, y_old=psi_S(R).

The odd Chebyshev quotient is an integer and gives

    S^2 V^2-(S^2-1)y_old^2=1,
    V=-c modulo f^2, V=-R modulo c.

Because gcd(c,f)=1, the integer

    T=(V+c+R f^2)/(c f^2)

is well defined. These identities say exactly V=f^2(cT-R)-c. Its numerator
and denominator are positive, so T is even positive, although positivity
is not required in the new domain. Choose centered y=y_old-B and centered
tau=tau_old-E(c-eta). They may be signed, as the domain permits.

This fresh auxiliary choice does not alter the native witnesses or first
Pell coordinates. It preserves the canonical determinant and eta*zeta
positivity, so a new shared-positivity certificate exists. Canonical
q=2^t with t odd has J=1 modulo3; canonical W/4 is a power of4 and is
also 1 modulo3. Thus J=3J3+1 and W=4(3w3+1) retain integral parameters.
All new residuals vanish. No consistency assumption is used.

## 5. Exact degrees and coefficients

Let q1=3 beta J3, Y4=2v q1^3, X2=12w3 q1 and E6=X2Y4.
For quotient20, E=a-Y has leading form -Y4 and k has leading form -hY4.
The only degree12 residuals are auxiliary and joint. Their degree12
forms are f^4 R4^2 and -eta^2 h^2 Y4^2, where R4=q1^3(q1-F).
Thus the degree 24 polynomial part is

    f^8 R4^4+eta^4 h^4 Y4^4.

In particular [f^8 F^4 J3^12]P20=(3 beta)^12>0.

For quotient19, E6=1944 beta^4 J3^4 w3 v is degree6, and k has
degree 7 leading form hE6. The joint row alone has degree16, with
leading form -eta^2 h^2 E6^2. Hence

    [eta^4 h^4 v^4 w3^4 J3^16]P19=1944^4 beta^16>0.

For quotient18, eta has leading form -Y4 hE6 and zeta has its
negative. The joint row has degree44 and all other rows have lower
degree. Its square gives

    [h^8 v^16 w3^8 J3^56]P18=2^32 3^64 beta^56>0.

The verifier computes degree upper bounds directly on every literal DAG
and checks these exact coefficients with all six fixed ports still
symbolic. Specialization to the actual tuple therefore retains the
certified degrees. Its finite modular checks are additional transcription
diagnostics only; they are not proofs of the unbounded Pell or compiler
theorems.

## 6. Dependencies and attribution

- Incoming Joint_Guards/guards/PROOF.md: residue-oriented signed native
  kernel, exact bootstrap order and canonical determinant composition.
- Incoming Joint_Guards/joint/PROOF.md: shared positivity and its exact
  source restoration.
- Source51/short/SQUARED_MODULUS_PROOF.md: the odd Chebyshev quotient
  and squared-modulus canonical auxiliary reconstruction.
- Retained SIGNED_DOMAIN_29.md, final ordinary-strong section: canonical
  i=Delta psi_A(cR)/c^2, and the need to derive f^2=1 modulo c only after
  rank recovery.
- Source34 coefficient recipe, source71 determinant constants, and their
  inherited native/compiler/K215 finite-refutation calibration.

The new work is the explicit composition, its noncircular soundness proof,
the choice to keep a as the free coordinate in P20, the centered auxiliary
row choices and the three measured endpoints. The CRT and norm-shear
ingredients predate this iteration. No complete new Lean/Rocq certificate,
object-language ZFC derivation, global minimum or worldwide priority claim
is made. The finite-refutation equivalence yields the requested no-zero
iff Con(ZFC) statement by negation, at the inherited ordinary proof level.

## 7. Exact transport parametrization saves one more coordinate

Replace the three free coordinates F,alpha,z by two coordinates C,z and
define, without division,

    F=(K0+W)C-z(q-1), alpha=q-F-C.

The transport residual is now the zero polynomial, so delete it. Every old
zero gives a new zero by retaining C=q-F-alpha and z; the two displayed
formulas restore F and alpha. Conversely every new zero restores the old
transport exactly. This is an integer-polynomial bijection of the full
zero sets (unlike the auxiliary CRT restriction, which uses canonical
reselection for completeness). All guard proofs apply to the restored
F and alpha, with no new positivity assumption.

Use the equivalent shorter index expression

    R=[q(q-F)-C](q^2-1)+(MC+qMF)J.

The identity (q-1)(q-F)+alpha=q(q-F)-C follows immediately from
alpha=q-F-C. The three new literal files omit alpha as a register when
it is not needed in evaluation; its restoration remains part of the proof.

For the 20-variable family, F has degree 2 and R has degree 5. B then has
degree 7, and the auxiliary residual has degree 14 while all other
residuals have lower degree. The new 19-variable polynomial has exact
degree 28, certified by

    [f^8 z^4 J3^16] quotient20_transport=(3beta)^16>0.

For the fully substituted a,E family, k's degree 7 term hE still dominates
the now-degree 5 R. The guard's highest forms therefore remain unchanged.
This gives 18 variables of exact degree 32 and 17 of exact degree 88,
with exactly the same leading coefficients as their unparametrized
parents. The verifier independently confirms the two representations of
R in its modular transcription diagnostics and verifies the exact
degree coefficients with all six fixed ports symbolic.

This transport step was supplied independently by the parallel research
worker in this iteration. Its mechanism is elementary monic elimination;
the contribution is its explicit use with the retained canonical CRT
and current signed/native guards, not a priority claim about polynomial
parametrization in general.
