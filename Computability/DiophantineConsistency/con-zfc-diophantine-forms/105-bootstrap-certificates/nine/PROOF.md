# Short local Laurent majorants and the complete nine-positive reduction

## 1. Result and scope

There are two literal polynomials in the nine strictly positive unknowns

    b, g, h, s, w, c, i, j, n.

Their complete circuits and fixed integer coefficients are supplied. The H1868
instance uses 456 live binary arithmetic operations and has exact degree 1,376,378.
The compact2082 instance uses 442 operations and has exact degree 1,520,186.

The new theorem proves both directions of the existential reduction from each
polynomial to its exact inherited source. The inherited ordinary source theorem
identifies source solvability with syntactic ZFC refutability. Consequently the
ordinary composed proof is formalizable in ZFC and proves that the displayed
polynomial has no positive zero if and only if Con(ZFC). Neither consistency nor
inconsistency is assumed. This package does not emit a new object-language ZFC
proof or proof-assistant certificate.

The main change is a very short majorant of sqrt(DF), specialized to the saturated
Pell certificate. It replaces a crude product bound without expanding the much
larger complete radical. A carrier successor permits an unconditional majorant
with only eight monomials. This is a local construction and tradeoff improvement;
no global minimum or worldwide novelty is claimed.

## 2. Complete coefficient and source specification

Each circuit has its own complete four-port tuple. They are not interchangeable.
The exact positive integers beta,K0,MC,MF are the unsigned little-endian values in
`ports/<profile>/`. MF is already shifted once. Each `fixed/<profile>/BINDING.json`
authenticates those values and every signed fixed numeral used by the circuit.
`coefficient_recipes` gives the exact integer-polynomial recipes from the ports.
The remaining two fixed leaves are powers of two with the literal exponents below.
Thus the fixed coefficients are finite numerals, not unknown parameters.

The tables under `source/<profile>/` specify weights w_l, targets q_l and three
integer-coefficient polynomials D_0,D_1,D_2. All sums below have these fixed finite
lists as their index sets. Put

    B = 2^kappa b^2,
    ell = sum_l B^w_l, Targets = sum_l B^q_l,
    Us = ell+g, Gs = (D_2(B)Us+D_1(B))Us+D_0(B),
    N0 = B^117, Mask = N0-1-(b-1)ell,
    Sc = g+N0(2Gs+Targets), Tc = Mask+N0(B-2)Targets,
    L = lambda b B^e, R = L(Sc+Tc+1)-Sc-1,
    N = 2^theta B^v, cap = b B^116.

The exact parameters are:

| Profile | kappa | lambda | e | theta | v |
|---|---:|---:|---:|---:|---:|
| compact2082 | 864026 | 1 | 2200 | 6480184 | 1162 |
| h1868 | 2134939 | 2 | 1986 | 16012032 | 1055 |

The new circuit preserves this entire prefix, not merely its values at sampled
inputs. The copied parents, literal extraction tables, source proofs and coefficient
bindings are pinned. The independent verifier checks a complete structural map of
all source registers. The source conclusions used below are R,N>=8 and b<=R,N on
every ambient positive assignment; the calibrated source/ratio equivalence; and
canonical witnesses with the extra bound used in Section 5.

For H1868 the source has 86 coefficient records and 81 stored kernel positions;
compatible identical coefficients are stored once. For compact2082 it is the
85-record gapNq source with its own repaired target layout. Nothing in the new
majorant identifies or mixes these different sources.

## 3. Polynomial definition

Set C=c+1. Define the unchanged ratio registers

    U=N^2 w, Y=N^2 s, M=RY, P=2M^2 U,
    K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw,
    J=4A-5, Q=3W1 C-2(W1^2-1),
    a0=1+(P^2-1)K^2, V0=PK,
    m=K^2(4cap-g)-16cap(C-KY)^2,
    Omega=Jm, E0=J(n+W1^2)+Q.

Define the saturated Pell registers

    delta=A^2-1, D=1+delta C^2, e0=iJC^2,
    F=1+delta D e0^2,
    Lambda=CD+1-A, G=A+F Lambda,
    Z=B1+(j-1)C, H=C+FZ, I=1+(G^2-1)H^2.

The new majorant and finalizer are

    T=iC^2[AJ(2D-C^2)+3C^2-4],
    V1=TGH, a1=4DFI, Theta=E0-Omega(V0+V1).

The single equation is

    (Theta^2+Omega^2(a0-a1))^2 - 4Omega^2 a0 Theta^2 = 0.       (1)

Every abbreviation is an integer polynomial. There are no square roots,
divisions, variable exponents, or additional quantified variables in (1).
The equivalent symmetric two-root norm follows from the exact identity

    (t^2+s(a-b))^2-4sat^2 = (t^2-s(a+b))^2-4s^2ab.

The inherited source bounds give A>=33280 on every ambient assignment. In
particular A>=2 and J>0. C>=2 holds by definition, before (1) is assumed.

## 4. The new majorant lemma

**Lemma.** For integers A>=2,C>=2,i>=1, with D,F,J defined above,

    T > 2 sqrt(DF) > 0.

**Proof.** Write t=C^2>=4. Direct integer-polynomial expansion gives

    T^2-4DF = i^2 t^2 Q(A,t)-4D,

where

    Q(A,t) = 20t(3t-4)A^3 - t(83t-116)A^2
             -10(7t^2-14t+8)A +109t^2-224t+116.             (2)

This identity has only 13 nonzero terms after collection. Write A=x+2,t=y+4.
The polynomial Q(x+2,y+4)-(x+2)^2 has the following coefficient matrix;
entry (r,s) multiplies x^r y^s.

| r \ s | 0 | 1 | 2 |
|---:|---:|---:|---:|
| 0 | 1344 | 816 | 117 |
| 1 | 3580 | 2188 | 318 |
| 2 | 2975 | 1852 | 277 |
| 3 | 640 | 400 | 60 |

Every coefficient is positive, so Q(A,t)>A^2 for A>=2,t>=4. Since i>=1,

    T^2-4DF > t^2 A^2 -4[(A^2-1)t+1]
             = A^2 t(t-4)+4t-4 >=12.

Also 2D-t=2+(2A^2-3)t>0, J=4A-5>0 and 3t-4>0. The displayed formula
for T therefore gives T>0. This proves the strict square-root inequality.

The restriction C>=2 is essential for this particular polynomial majorant.
At A=3,C=1,i=1 one has T^2-4DF=-308. The successor C=c+1 resolves the
boundary before the positivity argument, rather than assuming the carrier
range that the finalizer is meant to establish. This counterexample is an
explicit negative control in the verifier.

Since D,F,G,H are positive, G>A and H>C>=2, we have

    I=(GH)^2-H^2+1 < (GH)^2.

It follows that V1=TGH>2sqrt(DFI)=sqrt(a1). This is unconditional on the
entire new positive domain. Also V0^2-a0=K^2-1>0, so V0>sqrt(a0).

## 5. Soundness and completeness

### Soundness, with positivity recovered before integrality

Suppose (1) holds at positive integer inputs. First

    E0=Jn+(J-2)W1^2+3W1 C+2>0.

If Omega=0, (1) reduces to E0^4=0, impossible. Factor the symmetric two-root
norm over the reals. There are signed real roots r0^2=a0, r1^2=a1 with

    E0=Omega(V0+V1+r0+r1).

The strict majorants of Section 4 make the bracket positive for every choice
of signs. Hence Omega>0, and since J>0, m>0.

Now the inherited elementary margin argument applies: g<4cap,
|C-KY|<K/2, C>K and C>B1+W1. The last carrier bounds are not assumptions
in the majorant lemma. They are recovered only at this stage. For example
Y>=64 gives C>K from the approximation bound; K>=P+R, b<=R and
P=2R^2Y^2U give K>=B1+W1.

The two radicands are distinct. Indeed A^2>P, D>C^2, F>=A^2 and I>A^2.
Therefore

    DFI>C^2 A^4>K^2P^2>a0,

so a1=4DFI>a0. Put x=Theta/Omega=r0+r1. It is rational and nonzero.
The identity 2xr0=x^2+a0-a1 makes r0 rational, and then r1 rational.
A rational number whose square is an integer is an integer. Thus both
roots are integral; moreover r1/2 is a rational square root of the integer
DFI and is itself integral. The displayed factorization now implies J|Q.

The inherited saturated-Pell theorem states, for A>=3,1<B1<A,C>B1,J>=A,
that the specified DFI is an integer square exactly when C=psi_A(B1),
for some positive i and nonnegative j-1. Its proof includes pairwise
coprimality, Pell index folding, and simultaneous finite-period witness
construction. The required inequalities hold here. Hence

    a0 is square, C=psi_A(2R+1), J|Q, m>0.

These are exactly the retained ratio/source hypotheses. They give a zero
of the stated source and, by its retained calibration, a finite ZFC refutation.

### Completeness and the successor coordinate

Conversely take a positive zero of the inherited source. Its canonical ratio
witnesses satisfy the preceding four conditions and

    W1^2+Q/J<2D.

The Pell certificate has arbitrarily large compatible auxiliary witnesses;
one may use its finite-period construction or regenerate the old witnesses.
No arbitrary existential witnesses are silently identified. Since B1=2R+1>1,
the canonical C=psi_A(B1)>1, so c=C-1 is a permitted positive coordinate.
The new successor restriction therefore loses no source instance.

Choose positive integer roots u0=sqrt(a0) and u1=2sqrt(DFI), and put

    n=m(V0+V1+u0+u1)-W1^2-Q/J.

This is an integer. Also F>D because delta e0^2>1, so the new lemma yields
V1>2sqrt(DF)GH>2D. Since m>=1, the canonical bound makes n>0. Then
Theta=Omega(u0+u1), so one factor of the norm vanishes and (1) holds.
This completes both existential directions.

Negating this equivalence and composing with the original source/refutation
theorem gives the Con(ZFC) biconditional. The local changes do not assert
that the polynomial has no zeros, or that ZFC is consistent.

## 6. Exact degree, including all cancellations

Let r=deg R, nu=deg N, a=r+4nu+2, and W=116. The source leading kernel
coefficient is exactly +1; the verifier checks its unique weighted leading
monomial without using a sample coefficient tuple. The complete specialized
source has nonzero leading coefficient. Thus

    deg A=a, deg Omega=5a+2W+3,
    deg V0=3a+r+1, deg E0=a+4,
    deg delta0=3a+r+2,     delta0=V0^2-a0=K^2-1.

The carrier translation C=c+1 preserves these degrees. Regard A,C,i,Z as
independent weighted coordinates of weights a,1,1,r. The relevant unique
weighted leaders are

    T:                     8 A^4 C^4 i,
    T^2-4DF:              60 A^3 C^8 i^2,
    GH:                  256 A^14 C^15 i^4 Z,
    V1:                 2048 A^18 C^19 i^5 Z,
    delta1=V1^2-a1:   3932160 A^31 C^38 i^10 Z^2.

For the last statement use the exact identity

    delta1=(T^2-4DF)(GH)^2+4DF(H^2-1).

The first term has strictly greater weighted degree than the second. Hence

    deg V1=18a+r+24, deg delta1=31a+2r+48.

Define

    Bsmall=E0^2-2E0 Omega(V0+V1)+Omega^2(delta0+delta1).

The exact universal identity for the whole final polynomial is

    F9=Bsmall^2+4Omega^2 V0V1 Bsmall
       +4Omega^4(delta0 V1^2+a0 delta1).                     (3)

Its four summand degrees are

    82a+4r+8W+108,
    72a+4r+8W+85,
    59a+3r+8W+62,
    57a+4r+8W+62.

The first is strictly greatest in both instances and has nonzero positive
leading coefficient, namely the leading coefficient of Omega^4 delta1^2.
Consequently the exact degree, not merely an upper estimate, is

    86r+328nu+8W+272.

| Profile | r | nu | Four summand degrees | Exact degree |
|---|---:|---:|---|---:|
| compact2082 | 8799 | 2324 | 1520186,1339193,1095110,1067715 | 1520186 |
| h1868 | 7943 | 2110 | 1376378,1212505,991534,966707 | 1376378 |

As a second check on degree attainment, the verifier binds the actual coefficient
numerals and computes nonzero leading coefficients for the specialization in
which all nine variables equal one indeterminate, modulo three primes. This is
a coefficient witness in addition to the exact degree/unique-leader proof;
random finite evaluations are not used as a polynomial identity proof.

## 7. Costs, inherited dependencies, and verification boundary

Each live addition, subtraction, multiplication, scalar multiplication and
square costs one. Fixed numeral leaves and reuse cost zero. The successor
C=c+1 and scale a1=4DFI are included. There are no hidden quantified registers.
The exact counts are

| Profile | Additions | Subtractions | Multiplications | Total |
|---|---:|---:|---:|---:|
| compact2082 | 159 | 22 | 261 | 442 |
| h1868 | 155 | 22 | 279 | 456 |

The 456/1376378 point dominates the previously reviewed 475/1379730 point
on these two measures and uses the same original31 tuple. The 442/1520186
point trades cost against the current 433/1628768 compact54-sharp point.
The different domain, variable count, coefficient payload size and degree
measures are not collapsed into a claim of global simplicity.

The independent standard-library checker checks literal parent hashes,
source-prefix identities, every fixed numeral and its four-port recipe,
all new register identities, both universal norm identities, the positive
coefficient proof, topology/liveness/counts, exact degree and deterministic
regeneration. Normal and optimized runs agree. An altered majorant gate
and the invalid C=1 boundary are rejected. The checker does not import the
builder and does not search for a zero.

The copied ordinary source proofs remain the unbounded dependencies:
`saturated-proof.md`, `ratio-proof.md`, `source65-proof.md`,
`h1868-source-proof.md`, `h1868-full-soundness.md`, and the whole-tuple
coefficient-calibration documents under `inherited/`. The full native
compiler to refutation bridge is inherited rather than re-proved in this
contribution. A new Lean/Rocq or sealed object-ZFC derivation is not supplied.
