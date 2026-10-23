# Independent review of the two-root integer composition

Status: final two emitted polynomials pass the separate arithmetic checker.
The primary has 494 operations and exact degree 3,507,876; the lower-cost
companion has 490 operations and exact degree 3,547,076. The JSON receipt
pins their exact bytes. Both have ten unrestricted integer unknowns.

The final independent audit verifies 44,931 isolation interactions, 240
full-formula modular replays, 390 signed congruence fixtures and 1,426
small-block carry cases. It independently expands both affine source
transformations, checks the row orientations, authenticates every native
and derived fixed payload, and supplies three nonzero degree witnesses
per candidate.

## Mathematical soundness review

The ten inputs are unrestricted integers. The fixed source uses a coherent
four-port tuple, not a mixed tuple. Its inverse affine source changes are
valid only on the positive common-zero set, which is exactly the interface
needed here. In particular, the N-q gap remains positive because old N=q^3
and q>=2. The transformed sources already contain the two incoming row
operations; they must not be applied again. The primary mirror layout also
negates row 2. Multiplication by -1 is invertible and does not change the
common zero set. Its three kernel leaders are all positive, so each
kernel is positive at the large base independently. The companion instead
uses strict quadratic-over-linear and quadratic-over-constant dominance.
These are distinct valid positivity arguments; the primary does not have
the strict degree gap used for the companion.

The integer parameter b=6t+4 is even, nonzero, at least two in absolute value,
and 1 modulo 3. The register substitutions g=bg0, h=bh0 and
k=b(3k0+2) are essential, not arbitrary completeness restrictions. The source
word retains only positive positions. Consequently its value at the origin
is still nonzero, and every encoded positive source zero has g divisible by
b^2 on the cofinal power-of-four branch.

For the leadless code, the population mask is T'=T-2. Position zero is not
a source coordinate, so the original mask has both low bits set. The second
low bit is cleared without a borrow. Before a final zero one knows only
that b is even, not that 4 divides b. The soundness proof correctly postpones
the AND-equivalence assertion until the guard has recovered b as a positive
even square. At that point 4 divides b and hence g; since the remaining
part of S is a multiple of the large base, bit 1 of S is zero. Clearing
that mask bit therefore does not affect S AND T. It reduces mask population
by one. Removing the old leading block reduces the threshold by another
factor two. The new threshold is exactly the old one divided by four.

Unconditionally, the leadless formula
X=N(S+T'+1)-S-1 gives X congruent to T' modulo 3, not to T'-1.
Here T'=0 modulo 3, so 3 divides X. Also X is odd and
X+1=-g modulo b^2. These statements hold before any sign assumption.
They imply K=0 modulo 3b, Q=1 modulo b^2 and modulo 3, and
D=0 modulo 4b. Thus gcd(b,Q)=1 and Q is odd and nonzero.

Put r=bQ and a=r+(3Delta-1)(rz)^2, d=DFI. Then a/b is odd and d/b
is even. Hence a and d differ on every integer assignment, independently
of whether either is nonnegative. This excludes the zero signed-root sum
in the quartic two-root norm without a magnitude estimate or a separating
weight.

The two-root implication itself is elementary and unconditional: if
(q^2-a-d)^2=4ad and a!=d, then q!=0. Setting
u=(q^2+a-d)/(2q), v=q-u gives u^2=a and v^2=d. Rational square roots of
integers are integral. No preliminary use of real square roots is needed.
The polynomial center therefore implies both square predicates and
Sigma divides Theta. When Sigma=0, Theta remains nonzero: S=2A-5 is odd
and nonzero, while (x^3-x-1)(x^2+23) has no rational root. This deals with
all zero spectator branches before applying a bridge theorem.

The guard factorization a=r[1+(3Delta-1)rz^2] has coprime nonzero factors.
Nonzeroness uses |r|>=2 and z!=0. If a is square, both factors are signed
squares of the same sign. Since r=1 modulo 3, it cannot be a negative
square. Thus r and the bracket are positive squares. Applying the same
argument to r=bQ, using gcd(b,Q)=1 and b=Q=1 modulo 3, gives positive
squares b and Q. If Delta<=0, its bracket is at most 1-r<0, a contradiction.
Hence Delta>0. Its literal formula forces g>0, K!=0 and g<2cap. If l=0,
then P=0 and Q=1-K^2<=0, contradicting Q positive. Thus the omitted old
factor f^2 l^2 is indeed nonzero (old f=2t+1).

All of these recoveries precede the invocation of the inherited Sun
reverse bridge. That bridge, and not the finite audits, yields the
power-of-two base and binomial divisibility. The low-mask and signed-borrow
source theorem then produces a common positive source zero.

## Completeness review

Choose the existing cofinal source branch b=4^s, s>=1. The encoded word is
multiple of b^2 because all variable positions are positive; therefore
X+1 is a multiple of b^2, and X remains odd. The constructive Sun witnesses
are C=u_(2X+1)(A), K=u_(X+1)(P). Even Lucas indices imply P divides K;
odd Lucas indices imply C+1=0 modulo A^2. Since A,P carry the required
powers of b and v2(P-2)=v2(A-2)=1, the inherited quotient equations force
b divides h and b divides k. Reduction modulo 3 forces k/b=2 modulo 3.
These are the exact restrictions imposed in the polynomial.

With b,Q positive squares and Delta>0, 3Delta-1 is positive nonsquare
(it is 2 modulo 3). Pell gives z!=0 making a square. The inherited modified
Lucas interpolation theorem then permits xi to be a multiple of this z and
permits the required residue of y. The root of the intersective quintic
modulo xi gives Sigma divides Theta; an integer center makes the norm zero.
The local-root statement is justified prime by prime: the cubic has
 discriminant -23, the quadratic covers the irreducible-cubic primes,
23 has the simple cubic root 3, and -23 is a square in the 2-adics.
These choices do not fix z after the Lucas interpolation has been used.

## Arithmetic checks and limitations

The authored independent checker imports no builder or upstream program.
It authenticates all four native payloads, reconstructs the exact symbolic
source recipes and actual integer kernels, checks every same-degree target
interaction, evaluates the literal circuit against separately written full
formulas, checks graph liveness and binary operation counts, and proves
exact degree by a syntactic upper bound attained by a nonzero diagonal
coefficient modulo each of three primes. A nonzero residue is used only
as a witness that an integer coefficient is nonzero, not as an upper-bound
argument. It also checks signed congruence fixtures and exhaustive tiny
carry identities. Normal and optimized Python runs are intended to have
identical results because checks do not use assert.

No flaw has been found in the newly composed arithmetic proof. The native
compiler/refutation equivalence, constructive Sun bridge and Lucas
interpolation remain identified inherited dependencies. This review is not
an end-to-end Lean/Rocq certificate, an independently reconstructed proof of
those external theorems, or a proof of consistency.
