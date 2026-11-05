# A 66-operation consistency polynomial by a squared-modulus quotient

## 1. Result and scope

At repository commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f`, the explicitly
stated arbitrary-degree operation record is the 15-positive-variable,
67-operation, degree-155 polynomial P67.  The construction below gives a
15-positive-variable polynomial in **66 binary operations**, of exact degree
**157**, on the identical complete coefficient tuple.  The reduction is a
surjective existence reduction: it does **not** preserve the same set of
assignments to the auxiliary quotient and ordinate.

The ordinary mathematical compiler proof, the fixed coefficients, and the
K215-to-ZFC calibration are inherited.  The new argument is elementary and
formalizable in ZFC, but has not been checked by Lean/Rocq here.  Consequently
the combination proves, at the same ordinary mathematical proof level as
the inherited explicit polynomial,

    ZFC proves (P66 has no strictly positive integer zero) iff Con(ZFC).

No consistency assumption is used.  This is a new bounded operation-count
improvement, not a proof of global optimality or a reduction below nine
natural variables or ten unrestricted integer variables.

## 2. Polynomial definition

Keep the fifteen positive coordinates and all polynomial abbreviations of
`upstream/INHERITED_P67_PROOF.md`, section 1, with one change:

    V = f^2 (c T - R) - c.

Thus, writing S = i Delta c^2 and A = a+2, the factors are

    N0 = tau^2 - (X Y^2)(X Y^2+1) k^2,
    N1 = D^2 - Delta c^2,
    Na = S^2(V^2-y^2)+y^2,
    Nk = k-hE-R,
    Nt = (K0+w)C+(q-F)-z(q-1),
    Nstrong = Delta f^2-S^2.

The single equation is

    N0 N1 Na Nk Nt Nstrong - Delta = 0.

The new positive variable T occupies the old T slot; no additional variable
is introduced.  Its meaning changes.  The literal four-gate replacement is

    cT = c*T;
    inner = cT-R;
    scaled_inner = f^2*inner;
    V = scaled_inner-c.

The old five gates computed c(Tf-1)-Rf^2.  The precomputed f^2 is shared with
the retained strong factor in both circuits.

## 3. A polynomial Chebyshev congruence

Define the usual integer Pell polynomials by

    chi_t(0)=1, psi_t(0)=0,
    chi_t(n+1)=t chi_t(n)+(t^2-1)psi_t(n),
    psi_t(n+1)=chi_t(n)+t psi_t(n).

For r>=0 there is an integer polynomial Q_r such that

    chi_t(2r+1)=t Q_r(t^2).

The recurrence is

    Q_0(X)=1, Q_1(X)=4X-3,
    Q_(r+1)(X)=(4X-2)Q_r(X)-Q_(r-1)(X).

It proves both identities

    Q_r(0)=(-1)^r(2r+1),
    Q_r(1-a^2)=(-1)^r psi_a(2r+1).                 (1)

For the second identity, psi_a(2r+1), as a sequence in r, starts with
1,4a^2-1 and satisfies the recurrence with coefficient 4a^2-2.  Substitution
X=1-a^2 in Q changes that coefficient to its negative, giving (1) by induction.
These are polynomial identities over the integers.  They therefore hold
modulo every positive integer, including a square modulus.

**Squared-modulus reconstruction lemma.**  Suppose A>1, R=3 mod4,
c=psi_A(R)>0, Delta=A^2-1, and i,f>0 satisfy

    f^2=1+Delta i^2 c^4.

Put S=Delta i c^2, and define

    V=chi_S(R)/S, y=psi_S(R).

The quotient V is a positive integer, and

    S^2(V^2-y^2)+y^2=1,
    V=-c mod f^2,
    V=-R mod c.                                    (2)

Indeed S^2=Delta(f^2-1), so S^2=1-A^2 mod f^2.  Apply (1) with
r=(R-1)/2 odd to obtain the first congruence in (2).  Since c divides S,
the constant-term identity gives the second congruence.  The norm equation
is the Pell identity chi_S(R)^2-(S^2-1)psi_S(R)^2=1.

Also gcd(c,f)=1 and f^2=1 mod c.  Consequently V+c+Rf^2 is divisible both
by f^2 and by c, hence by their product.  Thus

    T = (V+c+Rf^2)/(c f^2)                          (3)

is a strictly positive integer.  Equation (3) is exactly

    V=f^2(cT-R)-c.

The older quotient used the modulus f and denominator cf.  Using f^2 gives
a quotient divisible by f and removes the multiplication R*f from the
equivalent factored old expression f(cT_old-Rf)-c.

## 4. Soundness

For every integer assignment, the exact polynomial identity is

    P66(...,f,T,...)=P67(...,f,fT,...).              (4)

Every other supplied coordinate and fixed coefficient remains identical.
The identity holds before any equation or positivity condition is imposed.
For a positive new tuple, fT>0; hence a new zero gives a positive P67 zero.
The inherited soundness theorem therefore supplies a finite ZFC refutation.

## 5. Completeness and the phase R=3 modulo 4

The inherited compiler theorem supplies a positive P67 zero for any finite
ZFC refutation.  Its Pell recovery gives c=psi_A(R) and the normalized strong
equation f^2=1+Delta i^2c^4.  Its native decoding also gives

    q=B^N, J=1+B+...+B^(N-1),
    (C-1) AND (MC J+1)=0,

where B is divisible by 4 and MC=2 mod4.  Hence q=0 mod4, J=1 mod4, and
MC J+1=3 mod4.  The disjointness condition forces the two low bits of C-1
to vanish, so C=1 mod4.  Since

    G=q(q-F)-C,
    R=G(q^2-1)+(MC+q MF)J,

we obtain R=C+2=3 mod4.  This phase is established from the authentic
compiler theorem; it is not assumed for arbitrary assignments of four
integer parameters.

Apply the reconstruction lemma at the same outer coordinates, f and i.
Replace only y and T by the positive values in (2)--(3).  The auxiliary
factor is again one; all five other factors retain their old values.
Thus the new polynomial is zero.  This proves existence-equivalence in both
directions.  It does not assert that an arbitrary old quotient T_old is
divisible by f.  A different auxiliary Pell ordinate is generally needed.

## 6. Exact degree and operation count

The six factor degrees are

    22, 18, 62, 7, 2, 46,

whose sum is 157.  Put Q=beta J, k0=eta+zeta and C1=Q-F-alpha.  The full
leading homogeneous polynomial is

    -8 Q^91 h gamma i^4 k0^13 w^13 s^26 T^2 f^4 (w C1-zQ).

For example, the coefficient of

    J^92 h gamma i^4 eta^13 w^13 s^26 T^2 f^4 z

is 8 beta^92, nonzero for the inherited positive beta.  Thus the degree
upper bound is attained.  The gate audit counts 38 multiplications,
15 additions and 13 subtractions, totalling 66; every gate, witness and
coefficient port is live.

The same substitution applied to the newer unscaled/SOS circuits gives:

| Parent operations/degree | New operations/degree | Scope |
|---|---|---|
| 67/155 | **66/157** | Scaled product, new operation-count record |
| 69/111 | **68/113** | Unscaled product tradeoff |
| 73/80 | **72/80** | Three squared residuals |
| 75/68 | **74/68** | Four squared residuals |

All have fifteen positive witnesses and the same fixed tuple.  The SOS
auxiliary residual increases from degree 28 to 30, but does not overtake
the highest residuals, so their total degrees remain 80 and 68.

## 7. Reproduction and remaining proof boundary

Run `python3 build_and_audit.py` (also checked with `python3 -O`).  It authenticates
the transformed source by a literal five-row match, verifies the exact local
pullback identity and the main-norm cancellation as sparse integer
polynomial identities, propagates leading homogeneous polynomials through
all literal gates, checks full liveness and operation counts, and emits four
JSON circuits with deterministic evidence.  It also performs 100 modular
full-circuit substitution diagnostics per circuit and 24 exact auxiliary
congruence/reconstruction examples.  The latter examples validate the
implementation but do not replace the universal proof in section 3.

The reconstruction examples use independent small Pell fibers, not claimed
K215 computations.  In particular no consistency witness has been searched
for, found or presumed.  The strong equation remains essential: merely
replacing f^2 by an arbitrary positive modulus would lose the inherited
Pell-rank soundness theorem.

The source manifests, coefficient payloads and inherited semantic proofs
must accompany this packet when it is integrated.  The fixed tuple is the
whole package-36 tuple with shifted MF_source, never a mixture of ports.
