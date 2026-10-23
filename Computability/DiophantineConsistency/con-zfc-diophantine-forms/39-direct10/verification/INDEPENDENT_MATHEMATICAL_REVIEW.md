# Independent audit: direct quadratic coding into the ten-integer equation

## Result of this audit

The candidate `generated/direct10.json`, SHA-256
`3fbbb2e2dbd1f651344875f741df0c03143a314dc160d472746e40a6b76cea26`,
passes the independent finite checks in
`verification/audit_independent.py`. The corresponding machine-readable
receipt is `verification/DIRECT10_INDEPENDENT_AUDIT.json`.

The circuit has exactly ten unrestricted integer variables, 786 live binary
arithmetic operations (539 multiplications, 222 additions, 25 subtractions),
and **exact total degree 267,823,432**. The latter is a proof by an integer
circuit degree upper bound and a nonzero coefficient at that degree after
the diagonal substitution of every variable by a common indeterminate:

| Prime | Coefficient of degree 267,823,432 |
|---|---:|
| 101 | 71 |
| 1009 | 993 |
| 1,000,003 | 398,031 |

Only one nonzero residue is needed to prove attainment. All fixed coefficient
values used in these certificates are derived from the actual native tuple,
reconstructed independently from the pinned literal tile list. All four raw
byte hashes agree with package 31's binding. These are not generic-port or
random-port degree tests.

The audit reconstructs all shifted residuals independently of the candidate
builder. It verifies all 528 unordered pair sums of the 32 weights including
zero, all 136 source monomial positions, and all 136 target matches. It also
compares the optimized source circuit with direct literal formulas at 54
finite-field fixtures, including f = -1, 0, 1, 2. Every node is live.

The downstream circuit is structurally identical to the existing package-31
ten-variable finalizer when its four source outputs `b`, `X`, `Y`, `Ccap`
are treated as independent input leaves. The common structural digest is
`8c36796cfae5982dcd2eda9b41b49857f1954e6f79f1ed54956dfabf6d1b96c2`.
Thus the new mathematical obligation is the replacement of the source coding;
no unannounced change to the Lucas, quintic-merger, positivity, or final norm
formulas is hidden in the arithmetic circuit.

## Mathematical audit of the changed source

Let q_j, 0 <= j < 22, be the 22 quadratic residuals after shifting the 31
original positive variables by 1. Reorder them so the original fifth residual
is last; that residual is E-X(a-E), and its value at all original variables
equal to 1 is 1. Write q_j(n) = sum a_(j,alpha) n^alpha and let H bound the
absolute values of every ordinary coefficient. Every |alpha| is at most 2.

Let 0 = w_0 < w_1 < ... < w_31 = t = 901 be the delivered weights. Their
unordered two-term sums are all distinct. With

    e(alpha) = sum alpha_i w_i,
    c_(j,alpha) = (2-|alpha|)! prod(alpha_i!) a_(j,alpha),
    qtarget_j = 2t + j(2t+1),

define

    D(B) = sum_j sum_alpha c_(j,alpha) B^(qtarget_j-e(alpha)).

All these exponents are nonnegative. Each channel is contained in its own
interval [qtarget_j-2t, qtarget_j], so **the D channels are disjoint**. The
coefficient bound is therefore |[B^k]D| <= 2H independently of 22, the number
of channels. The final, highest coefficient is the integer 2. It follows from
B-1 > 2H that D(B)>0; negative lower coefficients do not jeopardize positivity.

Put

    g = sum n_i B^w_i,
    E(B) = (1 + sum n_i B^w_i)^2.

The two-sum uniqueness, including w_0=0, says that the contribution to the
target of a source monomial alpha can only come from that same alpha in E.
Its multinomial coefficient cancels the factorial weighting to give

    [B^qtarget_j] E(B) D(B) = 2 q_j(n).

No adjacent channel can reach the target: an earlier D channel plus the
largest E exponent stops at qtarget_j-1, and a later D channel starts at
qtarget_j+1. The fact that convolution bands overlap at **non-target**
positions is harmless and must not be mistaken for target contamination.

For 0 <= n_i < b,

    |[B^k] E(B)D(B)|
       <= ||D||_infinity E(1)
       <= 2H (1+sum n_i)^2
       < 2H (32b)^2.

Since the fixed beta_source = 2^2134938 satisfies

    beta_source > 4*33^2*H,
    B = beta_source b^2,

every coefficient e_k of E D obeys |2e_k| < B. This is a global convolution
bound. No factor 22 or factor 2 for overlapping convolution bands is needed.
The delivered symbolic bound derives H from the authentic tuple's bit lengths
without assuming cancellation of signed coefficient recipes.

Let h = qtarget_21+2t = 41467. The source integer is

    J = 2(1+g)^2 D(B) + B sum_(i=0)^h B^i.

For sparse g the uncarried coefficient at every position 0 through h is
B+2e_i, an even integer strictly between 0 and 2B. When carrying from left
to right in base B, the incoming carry is 0 or 1 at every position. At a
target, adding a digit B-2 without binary carries is possible exactly when
the digit of J is 0 or 1. This occurs exactly when e_i=0: if e_i is positive,
the reduced digit is at least 2, while if e_i is negative it lies between
2 and B-1. Thus the simultaneous target mask detects precisely all 22
equations q_j(n)=0. This also covers both possible incoming carry values;
it does not presume the entire coefficient list is nonnegative.

## Size and boundary conditions needed by the inherited bridge

Write cap=b B^t, N0=B^(t+1), N1=4B^(h+1), N=N0 N1. Assume f != 0 and
b=1+3f is a square. Then b is a positive square and f>0, hence b>=4.
If also b is a power of two, B is a power of two and so are N0 and N.

The fixed exponent 2134938 is even. Therefore B is 1 modulo 3, since b is
1 modulo 3. Consequently N=4B^(t+h+2) is 1 modulo 3, so the new
X=(N-1)R remains divisible by 3, as required by the inherited bridge.

For any integer 0<=g<2cap, one has g<N0 because 2b<B. Let Tcode be the
low sparse-digit mask plus the shifted multi-target mask. The masks have
disjoint positions, every digit lies in [0,B), and the upper target is below
h, so 0<=Tcode<N. This statement does not yet assume sparse g.

The already proved D(B)>0 gives J>0 even for nonsparse nonnegative g. An
elementary upper bound using 1+g<=2b B^t and
D(B)<=2H (B^(qtarget_21+1)-1)/(B-1) yields

    2(1+g)^2 D(B)
       < [16H b^2/(B-1)] B^(h+1)
       < B^(h+1).

The geometric background is less than 2B^(h+1). Hence J<3B^(h+1)<N1,
and S=g+J N0 belongs to [0,N). Therefore Sun's carry/binomial lemma
applies to S,Tcode and N with no circular assumption about g's digits.

No binary carry in S+Tcode splits into (i) no carry between g and the low
mask and (ii) no carry between J and the upper mask. The low condition first
recovers the sparse expansion g=sum n_i B^w_i with 0<=n_i<b. The upper
condition then recovers all q_j(n)=0 by the target argument above.

Conversely, from any simultaneous nonnegative solution n, choose b=4^v
arbitrarily large, exceeding all n_i. Then f=(b-1)/3 is an integer and can
be arbitrarily large. The source solution n is not zero because q_21(0)=1.
Thus the encoded g is at least B^w_1>=b and is less than cap. Both masks
have no binary carries. The usual binomial bridge follows.

The resulting R=(S+Tcode+1)N+Tcode+1 is at least N+1; thus X>3b and
Y=N^2>max(b,256) hold with a very large margin. The cap has the prescribed
monomial form 2^(2134938*t) b^(2t+1), with positive fixed exponents.

## Scope, references, and remaining dependency

This audit establishes the changed source-coding argument and verifies the
literal circuit, fixed leaves, degrees, and interface. It does not independently
reprove the native K215/compiler theorem, the full quadratic-residual adapter,
or Sun's 2026 Lucas interpolation theorem. The finalizer is imported exactly
from package 31. An end-to-end Lean or Rocq theorem remains a separate task.

The relevant primary published source for the carry layer is Zhi-Wei Sun,
Further results on Hilbert's Tenth Problem, Sci. China Math. 64 (2021),
281-306, arXiv:1704.03504v7, especially Lemmas 2.1, 2.2, 2.4, 2.6 and the
proof of Theorem 3.1. These were read directly at
https://arxiv.org/html/1704.03504v7 . The local changes are the direct
quadratic channels, simultaneously masked targets, and finite B2 weights.

No reduction in the ten-variable count is claimed. This is a reduction in
degree and arithmetic circuit cost relative to the existing ten-variable
construction, not a global optimality theorem or a proof of Con(ZFC).
