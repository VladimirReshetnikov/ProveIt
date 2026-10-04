# Independent source-bound audit of the rational elliptic positive certificate

4 October 2026. Verdict: **PASS, with one non-substantive step-count wording erratum**.

The frozen certificate gives a correct conventional all-input proof, conditional
only on the explicitly identified Pell theorems. The positive-variable domains,
two time gates, two POWER modules, witness counts, and exact degree are correct.
No author program, physical simulator, upstream Lean program, or legacy checker
was executed. The fresh independent code in this audit directory was executed.

This is an arithmetic/source audit and a check of the geometry/physical interface.
It is not a new proof-assistant build or a re-audit of every physical collision.

## 1. Frozen source binding and preservation

Primary packet: `../elliptic-positive-certificate60-20261004/`.

| Source | SHA-256 |
|---|---|
| Certificate PROOF.md | `e93fdbefc3ba72e34c44e4f9d8a9b97e72027f72dc3ce53d54570113b7db5e5a` |
| Certificate PACKET_MANIFEST.json | `8585df2bcd6f227bf824b4dfa9610a1fc831bd0371994b28dfafdc055091e5d0` |
| Planar classification PROOF.md | `70eb8f8398d474c3343493fc88c006ce91951a2eb747c9b4133c5c481b666231` |
| Physical realization PROOF.md | `e0ddd64cdbbb5c7f448266ab58f1dfeb2868892ac0f230632b2337e4d0bed065` |
| Report 59 PROOF.md | `14c3d694d9e0c21f3ad3b125c0d1f2bbf47793e1283c9314aa3855ef60c89fc5` |
| Inert Pell source | `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a` |

Every entry in the certificate PACKET_MANIFEST and SOURCE_PINS was checked against
the actual bytes. The full snapshots bind 95 files across the certificate,
classification, physical packet, and two Report 59 dependencies. Before/after
byte counts, SHA-256 hashes, modes, and nanosecond mtimes agree. No source file
was rewritten, chmodded, touched, imported, or executed.

The author checker was inspected as text to understand its scope, but its receipts
were not used as proof. The fresh audit independently reconstructs all polynomial
residuals from the displayed equations, using SymPy rather than the author's
sparse-polynomial implementation. Arithmetic tests use exact Fractions and a
separate binary matrix-power implementation.

## 2. Matrix hypotheses, contact coordinates, and exact denominators

Certificate lines 7–17 and 36–61 are correct.

For A in SL2(Q), tr(A^-1)=tr(A)=p/q. With B=A^-1 and nonzero rational z,
the columns of S=[z,Bz] are independent: dependence would provide a real
eigenvector for a matrix with nonreal spectrum. Cayley–Hamilton gives
B²z=(p/q)Bz−z, hence BS=SC for C=[[0,−1],[1,p/q]]. This also verifies the
direction: C^n e1 represents the **backward** A-orbit, not the forward one.

An elliptic finite-order rational matrix has trace a rational algebraic integer,
thus an integer in (−2,2), hence −1,0,1. Each of these traces gives finite order
by its characteristic polynomial. Therefore reduced q≥2 is exactly the
infinite-order condition in the stated class.

Let V0=1, V1=p and Vk=p V(k−1)−q² V(k−2). Induction directly gives

    C^n e1 = (−q V(n−2), V(n−1)) / q^(n−1), n≥2.

For every prime dividing q, Vk ≡ p^k modulo that prime. Since gcd(p,q)=1,
gcd(Vk,q)=1, so the bottom coordinate alone has reduced denominator q^(n−1).
The joint denominator is therefore exactly q^(n−1). At n=1 the point is e2
with denominator 1, while n=0 is e1, also of denominator 1. A denominator
q^m determines the unique possible **positive** time n=m+1. The separate e1
test is indispensable and is present.

No assumption that q is prime, odd, squarefree, or a Euclidean-rotation
denominator occurs here. Negative p and zero numerator components cause no
problem. The rational contact basis does not require rational conjugacy to an
orthogonal rotation.

## 3. Quadratic power coefficients and extraction

Certificate lines 65–107 are correct.

Because Z²−pZ+q² has negative discriminant, it is irreducible over Q and its
nonreal root beta gives a unique integral representation beta^n=Cn+Dn beta.
Multiplication yields

    C(n+1)=−q² Dn,  D(n+1)=Cn+p Dn,  (C0,D0)=(1,0).

Thus Dn=V(n−1) for n≥1 and Cn=−q² V(n−2) for n≥2, while C1=0,D1=1.
In particular the numerator comparison in the outer gate is **q*u=Cn**, not
u=Cn. The point is (Cn/q,Dn)/q^(n−1).

Both roots have modulus q, and their separation is sqrt(4q²−p²)≥1. Therefore
|Dn|≤2q^n. For n≥2, |Cn|≤q²·2q^(n−1)=2q^(n+1); the n=1 case is zero.
For n=m+1 and P=q^m, the stated H=2q²P bounds both coefficients inclusively.

Write R=4H+|p|+1 and M=R²−pR+q². The polynomial remainder identity yields
R^n ≡ Cn+R Dn modulo M. For two coefficient pairs within [−H,H]^2, their
difference satisfies

    |delta_C+R delta_D| ≤ 2H(1+R) < M.

Indeed

    M−2H(1+R)
      ≥ R(R−|p|−2H)+q²−2H
      = R(2H+1)+q²−2H > 0.

A multiple of M with absolute value less than M is zero. Since 2H<R,
delta_C=−R delta_D then forces both differences to be zero. The modulus is
strictly positive, and the unrestricted signed quotient correctly permits
either congruence direction. Inclusive coefficient slack bounds are sufficient;
no hidden digit/nonnegativity assumption is made.

## 4. Primitive reduction, whole-q factorization, and acceptance

Certificate lines 111–191 are correct.

Clearing S^-1 with t>0 gives integer U,V,W and W=tN>0. The equations
U=hu,V=hv,W=hb with h,b>0 and e1*u+e2*v+e3*b=1 force
gcd(u,v,b)=1 and h=gcd(U,V,W). Conversely the primitive quotient always admits
signed Bezout coefficients. If an integer a>0 clears u/b and v/b, then b divides
au,av,ab and hence a by the Bezout equation. Thus b is exactly the joint
denominator. At x=0 this correctly yields u=v=0,b=1.

POWER(q,m) gives P=q^m. The conditions r=qk+s, s+t=q, with k≥0 and s,t>0,
are exactly Euclidean remainder conditions 1≤s≤q−1. Hence q does not divide r.
Repeated division gives the unique b=q^m r, r>0, q∤r. It is permissible for r
to share prime factors with composite q; nothing uses additive valuations.

For d=0, the first acceptance value is

    (u−b)^2+v^2,

which vanishes exactly at time zero. The second is

    (r−1)^2+(q*u−C)^2+(v−D)^2.

After the extraction theorem, it vanishes exactly when r=1 and the reduced
point equals the positive-time candidate C^(m+1)e1. In particular n=1,
m=0,b=P=r=1,C=0,D=1 correctly rejects e2. The e1 gate rejects e1 even
though its positive-time candidate is e2. Positive J0,J1 turn nonzero sums of
squares into strict acceptance, without selectors or an extra existential
inequality gadget.

For the kernel, Delta=d with natural d says exactly that the input lies in the
closed rational ellipse. Interior points have d>0, making both gates positive;
boundary points have d=0 and are accepted exactly on simultaneous orbit
avoidance. Outside points have Delta<0 and no natural d. For pure avoidance,
omitting d and replacing d² by zero has precisely the claimed meaning.

Every variable domain matters and is correctly supplied: six outer naturals,
seven strictly positive values, and eight signed values per contact. A natural
z becomes one positive leaf minus one, and a signed integer becomes a
difference of two positive leaves. These substitutions cover all required
values without adding equations. Nonprimitive input encodings, the origin,
duplicated contacts, and overlapping contact orbits are all harmless.

## 5. POWER specialization and natural subtraction

Certificate lines 195–229 are a correct specialization of the pinned inert
source. This audit reads the actual theorem statements, including all domains
and inequalities, rather than accepting the module as an exponentiation oracle.

The source is the stated Mathlib/NumberTheory/PellMatiyasevic.lean at commit
ac77769fabe23cb237559e7f56578dbead91499f; this audit checks the provided file
hash and statement specialization, not the entire historical commit provenance
or a fresh Lean build.

### 5.1 Pell index statement, source lines 760–766

Map source (a,k,x,y,u,v,s,t,b) to
(alpha,k0,x_p,y_p,u_p,v_p,s_p,t_p,beta). The module has alpha,beta≥2 and
k0=e+1≥1. Equation 9 supplies k0≤y_p, so the zero-index alternative
(x=1,y=0) is excluded. The three Pell equations, beta≡1 mod 4y, beta≡alpha
mod u, v>0, y²|v, s≡x mod u, and t≡k0 mod 4y are precisely equations 1–8
and the positive domains. Their congruences are represented by differences of
nonnegative multiples with no omitted sign.

### 5.2 Power statement, source lines 860–864

Map source (n,k,m,w,a,t,z) to (B0,k0,B0*out,w,alpha,M,g).
The positive-base and positive-index branches apply. Equations 10–11 give
w≥B0 and w≥k0; equation 12 gives the essential strict M>B0*out; equation 13
is the auxiliary Pell condition; equation 14 is the modulus identity;
equation 15 is the remaining congruence. The theorem implies
B0^k0=B0*out. Since B0≥2, cancellation yields out=B0^e.

The natural subtraction translations are exact. For natural a,b,
a truncated-minus b=1 iff a=b+1. Thus converting the outer Pell identities
to ordinary integer equalities loses no solutions. The inner differences
alpha²−1, beta²−1 and (w+1)²−1 are nonnegative because alpha,beta,w≥2.
Finally g>0 and equation 13 imply alpha²>w² and hence alpha>w≥B0, so the
source's alpha truncated-minus B0 equals the displayed integer alpha−B0.

### 5.3 Completeness and strictly positive auxiliaries

The constructive source statements supply the natural auxiliaries. The required
extra positivity follows, rather than being assumed:

* g=0 would force alpha²=1, contradicting alpha>1
* Pell x,u,s must be positive; y≥k0≥1 and the source gives v>0
* y²|v with y,v>0 makes q_v>0
* beta>1 and beta≡1 modulo 4y make q_b=(beta−1)/(4y)>0
* t≡k0 modulo 4y, with 1≤k0≤y<4y, excludes t=0
* strict M>B0*out supplies J_p>0
* every integer congruence quotient is a difference of two naturals

The shifts alpha=alpha_leaf+1 and beta=beta_leaf+1 cover every integer ≥2.
All eleven natural slack/quotient variables admit their positive shifts.
Consequently the 26-positive-leaf formulation is equivalent to POWER for
every B0≥2 and e≥0, including e=0.

There is no circular base hypothesis: q≥2 is fixed, and R=8q²P+|p|+1≥2
already follows from the positive output leaf P before invoking either module's
semantic correctness. The second exponent m+1 is natural.

As additional independent evidence, this audit constructs actual module
witnesses directly from the source's Pell/CRT formulas for six cases:
(B,e)=(2,0),(2,1),(3,0),(3,1),(4,0),(6,0). Each has all 26 leaves positive
and all 15 residuals exactly zero. The largest sample leaf is 34,887 bits.
These samples support the translation but do not replace the source theorem
for unbounded exponents.

## 6. Reconstructed coefficients, degree, and ledgers

Certificate lines 233–251 are correct. Per contact the exact leaf count is

    6 natural leaves + 7 positive leaves + 2*8 signed leaves
       + 2*26 POWER leaves = 81.

Outputs P,T are already included in their module's 26 leaves. H,R,m+1,k0,m0,
input linear aliases, and parameter shifts are expressions, not hidden leaves.
The equation count is 14+2*15=44. The shared radius variable/equation adds one
of each, giving 1+81J and 1+44J. These are witnesses, separate from input arity.

After every adapter and alias, outer residuals have degree at most three;
the extraction quotient times R² supplies the possible cubic term. POWER
residuals have degree at most six. This remains true when the base is affine
in another module's output. POWER equation 13 has degree-six term −w^4 g²,
and no substitution changes those two directly positive leaves. Its squared
residual contributes w^8 g^4 with coefficient 1. A real sum of squares of
leading homogeneous forms cannot cancel identically. Thus for nonempty J the
literal sum-of-squares polynomial has exact degree 12.

The independent exact reconstruction found:

| Schema | Inputs | Witnesses | Residuals | Monomials | Degree |
|---|---:|---:|---:|---:|---:|
| One-contact five-input kernel, p/q=−5/6 | 5 | 82 | 45 | 847 | 12 |
| One-contact five-input avoidance, p/q=−5/6 | 5 | 81 | 44 | 725 | 12 |
| Two-contact three-gap kernel, p/q=1/2 | 3 | 163 | 89 | 1590 | 12 |
| Actual physical-fixture three-gap kernel | 3 | 82 | 45 | 812 | 12 |

All POWER w^8 g^4 coefficients are exactly 1. Full positive adapters and all
expanded residuals are in RECONSTRUCTED_SCHEMAS.json; that list explicitly
defines the polynomial as the sum of the residual squares. The 847 count
agrees with the author receipt, but is independently reproduced rather than
copied or obtained by running its code.

The optional paid Cantor decoder is also counted correctly. Its three positive
gap variables and one natural intermediate contribute four leaves; the two
quadratic pairing equations add two residuals. The one-positive-input kernel
therefore has 5+81J witnesses and 3+44J residuals, still degree 12. It is a
different input convention, not a free three-to-one input reduction.

## 7. Geometry and physical three-gap interface

The classification proof lines 176–210 constructs rational symmetric Q>0,
positive rational r², and nonempty rational contacts using

    Q=S^(-T)[[1,tr(A)/2],[tr(A)/2,1]]S^-1, S=[v,Av],
    d_i=h_i Q^-1 h_i^T,
    r_i²=b_i²/d_i,
    z_i=(b_i/d_i)Q^-1 h_i^T.

Taking the minimum radius and its contacts gives exactly the strict boundary
orbit-deletion predicate used here. The classification's contact basis and
denominator argument at lines 250–265 agree with this certificate, including
the n=0/n=1 distinction. The finite polynomial-sign obstruction is not in
conflict with an existential integer-witness polynomial.

The physical proof lines 9–18, 210–236 and 254–270 supplies the needed exact
bounded open rational chamber and normalized return w↦Aw. Its global scale
lambda cancels on the normalized section. For three positive gaps,

    Dphys=g1+g2+g3, x=g1, y=g1+g2,
    w=((x−Dphys/3)/Dphys, (y−2Dphys/3)/Dphys).

Thus the certificate may use the integer linear aliases

    X=2g1−g2−g3,
    Y=g1+g2−2g3,
    N=3(g1+g2+g3)>0.

No normalization witness, rational-coordinate leaf, or additional equation is
needed. This is a specialization on the positive initial triangle; the claim
does not require those three positive gaps to encode every point in Q².

For a concrete source-bound check, the inert compiler fixture
`evidence/elliptic_conjugate_lambda_1.json` has SHA-256
`d83d30104b4736211ce011b9b4b25acd667c2815148936f459b15bbfcfa20868`.
Starting only from its matrix and guard rows, the fresh audit independently
reconstructs:

    A=[[3/5,−8/5],[2/5,3/5]], tr(A)=6/5,
    Q=diag(1,4), r²=1/45,
    z=(−2/15,1/30), J=1,
    L=45, G=diag(45,180), a=1,
    t=4, M=t[z,A^-1 z]^-1=[[-33,−12],[15,60]].

Every displayed quantity is checked exactly. Substitution into the full
three-gap certificate gives the 82-witness, 45-equation, degree-12 schema in
the preceding ledger. The audit uses the saved physical guard data as a
source-bound interface fixture; it does not claim that this arithmetic check
independently validates the entire physical word.

## 8. Decision complexity, scope, and the wording erratum

The polynomial-time conclusion at certificate lines 253–259 is correct.
After a rational basis change of polynomial bit complexity, the joint
denominator b has polynomial input bit length. Whole-q division determines
m≤floor(log_q b). Only e1 and, if r=1, exponent n=m+1 must be tested. Every
intermediate coefficient has magnitude at most 2q²b, so its bit length is
O(1+log b+log q). Exact rational 2x2 operations, gcds, divisions, and this
bounded recurrence therefore have polynomial bit cost, uniformly in A,z,x.

The geometric construction uses only fixed-dimensional rational matrix
operations, one rational candidate per supplied polygon row, and rational
comparisons. The number of contacts is at most the number of supplied guards.
Thus the elliptic strict-kernel decision claim is uniform in A,P,x. It does not
say that a physical compiler emits polynomially many guards, that all stable
branches are uniformly polynomial-time, or that Pell witnesses are efficiently
constructible. The decision algorithm never needs the large ordinary powers
used for the existential certificate.

**Erratum E1, minor:** line 257 says there are “at most log₂b divisions and
recurrence steps.” Read literally, this is false at b=1, where the candidate
is n=1, and generally the recurrence uses m+1 rather than m steps. Suggested
replacement:

> There are at most floor(log₂ b) successful divisions and
> 1+floor(log₂ b) recurrence steps, with one final divisibility test if needed.

The surrounding proof already gives n=m+1 correctly; this wording correction
does not change any theorem, polynomial, domain, ledger, or complexity class.
It should be recorded as an erratum or a newly versioned proof, preserving the
frozen source audited here.

## 9. Exact evidence and final boundary

The independent run passed:

* 2,508 reduced signed traces with 2≤q≤45
* 92,796 exact backward powers and 90,288 forward powers checked for direction
* 499,092 whole-base factorizations
* 24,276 rational-grid membership comparisons against complete bounded searches
* 350 rational contact-basis instances
* 24 exhaustive bounded-extraction searches
* Six explicitly constructed POWER-module solutions
* Four fully adapted sum-of-squares schema reconstructions
* Byte/hash/mode/mtime preservation for all 95 snapshotted source files

These finite tests are supporting evidence, not substitutes for the universal
arguments above. The mathematical dependency remains the explicitly pinned
Pell characterizations. No end-to-end formal verification, generic MRDP
invocation, arithmetic-DAG/gate count, unique/finite-fold witness claim,
small-height witness bound, physical simulation, or expanded realization scope
is inferred.

**Final finding:** no substantive correction is required for the frozen
positive-integer certificate or its stated geometric/physical interface.
