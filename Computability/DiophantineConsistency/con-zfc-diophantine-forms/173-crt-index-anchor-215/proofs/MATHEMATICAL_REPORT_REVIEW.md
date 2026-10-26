# Independent mathematical review of the CRT-anchor report

This is a separately assigned AI mathematical review of the report for the
215-variable quartic, carried out on 25 October 2026. It is not external
human peer review or a proof-assistant verification. The report was being
edited concurrently for clarity; this note concerns the stated semantic
construction and proofs, not a claim that the TeX file remained bytewise
unchanged during review. The printed-coefficient parser and exact projection
replay are separate finite audits.

## Findings

No substantive mathematical gap was found in the new argument reviewed.
The following points were checked independently.

### The integer constructor bound

For a positive integer s and integer inputs 0<=x,y<s, monotonicity puts
the largest constructor value at E(s-1,s-1). Direct calculation gives

    A(s-1,s-1)=8s^2-2s,
    E(s-1,s-1)=8s^2-2s+1<8s^2.

The other constructors are smaller. At s=t^e, t>=16 and e>=1, this is
strictly below t^(2e+1). All leaves, including constants 0 and 1, are
strictly below t. Therefore the depth recurrence is valid with strict
inequalities at every stage. The certified maximum depth 19 gives
label<t^(2^20-1), and L=t^(2^20) is sufficient. The report was asked to
state explicitly that s is an integer before inferring x,y<=s-1.

### Product separation, including equality at the carrier bound

The unequal-length argument is valid even though the premise side can
have 2t+1 factors: the smaller length r is at most t because the conclusion
side has at most t. Consequently F+1<=L^r<=L^t<=F is impossible.

For equal length m<=t, each coefficient of positive degree is in [1,F],
using binom(m,k)<=m^(m-k) and L>=m. A difference of corresponding
coefficients is thus in [-(F-1),F-1]. No factor two is needed, and
F=L^t is permitted. The constant coefficients cancel. The least-nonzero-
coefficient reduction modulo F proves polynomial identity; unique
factorization over Q gives label multiplicities. Empty products and
zero-label unit factors are handled separately and correctly.

For t>=128, K=t^4>=2^20*t, so F=t^K>=L^t. The proof does not rely
on a numerical accident at the minimum horizon.

### Signed powers and bootstrap order

The frame uses squares of every actual base, index, and proposed output;
it requires no postponed semantic sign. The signed anchor bounds all
classified indices before the orientation pool is used. The squared
orientation errors have a nonnegative small residue, including both
abscissa signs. This makes the canonical power lemmas available before
the front variables are interpreted.

The front's sign order is acyclic:

1. Positive t and K authenticate positive even F.
2. Even C and B*eta=C+F+1 force odd nonzero B. Independently H=2 mod 4
   gives |BH|>=2 for all signed representative tuples.
3. The BH request gives x>=0; the last endpoint excludes x=0.
4. The q block then forces y+1>=0; the affine odd-multiple equation
   excludes negative y, giving y>=F.
5. The endpoints give x>=F+1 and x>=2+(t+1)y.
6. Hence |q+1|>=2, and its block recovers all representative signs.
7. The signed-radix first digit authenticates B>0; then q,N are positive.

For the first digit, the coefficient bound (F+t)^t<=2^(t(F-1)) is
valid in this enormous range. Both the true low remainder and the
normalized candidate have total difference smaller than the modulus.
After the congruence B=binom(F+t,t) modulo q is obtained, |B|<|q|/2
and the true coefficient is less than |q|/32, yielding exact equality.
No positive-radix premise is used prematurely.

### CRT and the local bound

The factorial-free theorem uses both necessary directions: a sufficiently
large selector for every row, and a compatible row for every prime of B.
Both valuation arguments are valid. The range lemma, raw index condition,
and p^e>t recover the exact local index. The independent local polynomial
bound remains valid when F changes because its expression is unchanged.
The endpoint inequalities imply R0=2+t+x+y+F<2x and x>2^32, giving
R0^(2^23)<2^x by the stated dyadic estimate.

In completeness the precision is p^(2ex). Division by k! loses at most
k-1<x<=ex, including the strict quotient ranges with k=x. If an upper
argument is below k, its binomial is zero and satisfies the divisibility
without a separate positive-argument hypothesis.

### Beta coherence and the zero-state boundary

The same x,y and the local range 0<=S,S'<=y make overlapping beta states
equal, because each modulus is at least y+1. If y=F, the first endpoint
has remainder zero while the last has remainder one. Every selected
positive-weight row propagates a zero state, so this case is impossible.
Thus the initial state is F+1 and cancellation of intermediate positive
states is justified. The single-conclusion closure proof handles cycles
and repeated premises; it does not assume the certificate is an acyclic
ordered proof.

### Cofinal anchor completeness

The construction order fixes the proof, t,K,F,y,x,B,N and representative
residue classes before choosing the actual C. Since B and N^2 are odd,
the even representatives in C's class form an unbounded progression.
C can exceed all other already fixed indices. Only then are H,q and
the square frame chosen. Their size increase is harmless because the
radix uses the actual representative values.

The canonical Pell ordinate at the larger index dominates the finite
sum of other squared ordinates at the large positive frame center. Even
C gives even Y_C and odd X_C. The auxiliary index C*Y_C supplies the
required odd quotient J_Y/Y_C^2, and the two-modulus CRT supplies the
comparison center. All nonnegative slacks admit the stated ternary
representation by the three-square theorem applied to 4n+1.

## Quantifiers and inherited proof boundary

The formal claim is

    ZFC proves [not exists x in Z^215, P(x)=0]
               iff [not exists p in N, Proof_ZFC(p,falsity)].

Here Proof_ZFC is the effective syntactic proof predicate fixed by the
repository calibration. This is an internal arithmetical equivalence,
not a statement restricted to externally standard finite derivations.
No consistency, omega-consistency, or transitive-model assumption is
introduced by the arithmetic proof.

The least independently reproduced dependency remains the full C222/ZF
logical calibration, particularly the seed-to-quotient-to-internally-
well-founded-model lower direction. The entire Lean closure was not
rebuilt. Signed Pell classification and comparison-index theorems also
remain inherited unbounded results. The report states these boundaries;
finite tests and exact coefficient collection are not represented as
establishing those theorems anew.

## Source and license checks

The exact missing square-shell transport proof was recovered from the
pinned source-112 intake. Its 7,769 bytes have SHA-256

    a6c24442d6c79b747117aa89a26e51b37a8de7e6f159a45f2da01be112af2dc3,

matching source158's inherited provenance. The local file is
`proofs/SHELL_ENCODING_PROOF.md` in this audit workspace. All fourteen
inspected calibration files and the three source135 proof notes were
authenticated against Git blob SHA-1 values from the pinned commit;
their exact SHA-256 values are in `SOURCE_BYTE_PINS.json`.

The repository root and source packages 135,151,157,158,159 all supply
the same MIT No Attribution license, Copyright 2026 ProveIt Contributors.
Exact copies of these licenses and each package's attribution notice
are in this audit's `licenses/` directory. This observation concerns the
inspected source files and does not claim a license audit of every
transitive Lean dependency, which is not redistributed as a full closure.
