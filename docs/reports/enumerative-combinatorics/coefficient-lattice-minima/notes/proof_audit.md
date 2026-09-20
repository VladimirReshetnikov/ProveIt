# Proof audit

## Main invariant

For A=(0,1,q1,q1*q2,...) and the carry basis
v_j=(q_j-1)e_0-q_j e_j+e_(j+1), a relation c=sum z_j v_j satisfies

    sum_{i=1}^j a_i c_i = -a_(j+1) z_j.

The positive and negative partial weighted sums both lie in [0,a_j*d(c)],
so their difference has absolute value at most a_j*d(c), NOT twice that
quantity. Division gives q_j*|z_j| <= d(c). This factor of two is important:
d(c) is half the L1-norm.

## Integral generation

The coefficient of v_j at its highest coordinate j+1 is one. Reverse
elimination therefore uses integer coefficients. The final two-coordinate
remainder vanishes because a0=0 and a1=1. Full rank alone would not prove
that the basis spans the lattice over Z; this argument does.

## Filtration and ties

At bound H every coefficient whose radix exceeds H vanishes. Conversely,
each carry of radix at most H is itself a short vector. This proves equality
of the generated subgroups, including repeated radices and arbitrary radix
order. The subgroup is not the finite norm ball. The coordinate box is only
an outer bound on that ball; candidate vectors must still pass the norm test.

## Entrance equality

If a degree-Q vector has a nonzero coefficient with radix at least Q,
that radix is exactly Q, the coefficient is +/-1, and the degree is Q.
Equality in the partial-sum bound forces all negative mass to be Q copies
of a_j (after choosing a sign); the positive weighted mass a_(j+1) must be
one copy of a_(j+1), with all remaining mass at zero. The vector is exactly
+/-v_j. For larger multiples, equality alone would not imply this rigidity;
the +/-1 condition is essential.

## Sumset counting

All integers have unique mixed-radix digits and a top quotient. Carrying
from lower to higher denominations reduces the number of nonzero summands,
so the digit representation is minimum-length. Padding with zero determines
membership in hA. Distinct normal forms give distinct integers, preventing
representation-counting from being mistaken for set cardinality.

## Algebra

Generating the relation lattice does not automatically imply generation of
the toric ideal. The article separately proves that normal monomials have
distinct images in K[u,t], which gives ideal equality. The regular-sequence
proof works over any field by monic division and freeness over the remaining
polynomial variables; there is no characteristic-zero assumption.

## Exact growth onset

D=sum(q_j-1). At h=D-1, the top digit tuple contributes zero, so the affine
formula is already valid. At h=D-2 it would contribute -1; truncation changes
that to zero, producing a discrepancy of exactly +1. D=1 and rank zero are
handled separately.

## Claims deliberately limited

The first two minima and their general early sumset regimes were already
studied in the source. This draft targets full-list realization. The full
sumset formula is restricted to the constructed chain family. An explicit
pair of non-chain-equivalent sets with the same minima shows why the
restriction cannot be dropped.

No proof assistant was used. The code tests are exact finite checks, not
formal verification of the all-parameter proof.
