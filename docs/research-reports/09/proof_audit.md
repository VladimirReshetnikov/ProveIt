# Mathematical audit and dependency ledger

This ledger records the arguments actually supplied. “Proof supplied” means
a conventional proof, not an independent review or a proof-assistant result.

## Central dependency graph

1. Finite-prefix discrepancy inequalities.
2. The supremum-prefix metric on a single coarse-description class is
   complete and separable; finite modifications of every member are dense.
3. Local recovery: a fixed functional computing A on a dense subset of a
   nonempty open region implies that every description computes A.
4. Outside the common-information ideal, the success set of each functional
   is nowhere dense. Baire category gives simultaneous countable avoidance.
5. The bad relation “two fixed functionals compute the same non-core set” is
   nowhere dense in the product description space.
6. Finite-level Cantor fusion avoids all bad relations and the prescribed
   unary bad sets, producing a perfect family with exact common lower cones.
7. A separate external-center version of the finite-prefix search proves that
   arbitrarily good Z-computable approximations force the core below Z.
8. Guarded c.e. diagonalization produces an explicit complete X with such
   computable approximations but no computable actual coarse description.
9. Nonzero class + exact pairs proves no least degree and no countable
   coinitial family. Robust block coding gives the relative examples.

## Critical checks

### Which metric?

The asymptotic pseudometric delta is zero between any two elements of C_X.
It cannot support the argument. The proof instead uses

    d(D,E) = sup_{n>=1} |(D symmetric-difference E) intersect [0,n)| / n.

A d-Cauchy sequence stabilizes every bit and converges in d, not just in
ordinary Cantor topology. The limit remains in C_X by the triangle bound.

### The finite-prefix search

An accepted finite computation must obey all finitely many prefix-density
bounds, not only the density bound at the final use. Patching its string onto
the center gives an actual member of the required open region. Density then
forces the accepted value to be correct. A genuine total computation in the
open region proves termination.

The finite correction to the center and the rational radius are hard-coded
constants for an existential Turing reduction. No uniform selector for those
constants is claimed.

### Product nowhere density

Assume the bad relation is dense on U x V and select one pair with output A
outside the core. A disagreeing finite computation in U, paired with a fixed
finite computation of the selected second oracle in V, would give an open
rectangle missing the relation. Thus every convergent first-coordinate output
is forced to equal A. The projection of the bad relation is dense in U and
makes the first functional total. Local recovery contradicts A being outside
the core.

This does not interchange “for every pair, there exists an output” with a
uniform choice of output. Density and fixed finite computations supply the
necessary consistency.

### The perfect set

All ordered distinct node pairs and all bounded-index functional pairs are
handled at each finite level. Shrinking preserves earlier requirements.
Nested closed sets of vanishing diameter have unique limits by completeness;
compactness of metric balls is not assumed. Continuity into ordinary Cantor
space then proves the image is a usual perfect set.

Singleton avoidance of the countable set I_X intersect C_X ensures that two
selected paths cannot be Turing comparable. Without that additional unary
requirement, the exact-pair equality alone would not always force
incomparability when the core is nontrivial.

### Approximate centers outside the class

A computable approximation C_0 need not be a coarse description. The search
is carried out using C_0, but its accepted string is patched onto a genuine
description Y for the correctness proof. The two-center triangle estimate
keeps this genuine description inside the open set.

### Guarded diagonalization

For n in column R_e, X(n)=1 requires convergence with binary values of *all*
program inputs through n and value zero at n. If program e is not total
binary, its column has finite support below the first bad input. Otherwise
that column is the complement of a computable function. Each column is
computable individually; there is no claimed uniform list of its indices.

The map from a halting index p to a program that waits for p and then returns
zero gives a many-one reduction at input 2^{e(p)}-1. No time or complexity
bound on that reduction is claimed.

### Representative classes versus density-zero classes

C_X is only a subset of the uniform and nonuniform coarse-equivalence classes.
Equality of coarse-description mass problems proves that every selected path
is nevertheless a representative in both larger classes. A separate argument
proves those larger classes contain no computable representative.

Graphs code natural-number-valued representatives, so the common-lower-cone
argument applies to the original function-valued question as well.

### Minimal, least, and coinitial

A Turing minimal pair consists of two nonzero degrees with only degree zero
below both. This is not the same as two minimal members of a coarse class.
The no-countable-coinitial result does not rule out an uncountable family of
individual minimal representatives.

### Uniformity

The majority block decoder recovers the underlying set up to a finite
correction, proving a nonuniform Turing reduction. The least-representative
image characterization is asserted only for nonuniform coarse classes.
The uniform-class counterexamples use identity coarse reductions between
coarsely equal sets, not a silently uniformized exact decoder.

### Relativization

The relative guarded set X_Z is c.e. in Z and Turing equivalent to Z'.
Interleaving X_Z with robust block coding of Z forces all descriptions to
compute Z while retaining arbitrarily accurate Z-computable approximations.
This gives core exactly the lower cone of Z, with no Z-computable coarse
description. Consequently every coarse representative is strictly above Z.

## Remaining uncertainty

No gap was found in the internal mathematical audit. This is not independent
expert confirmation. The stronger exact-pair and perfect-family statements
may already be known in another form; novelty was not established. No Lean
kernel verification was performed, and no effective bound is given for the
perfect-set code. The effective-dense question is outside the scope of the
proof.
