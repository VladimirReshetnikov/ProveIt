# Second mathematical review of the graph compiler

Reviewer: a separately tasked research agent in the same AI-assisted workflow.
This is not external human refereeing, a new proof-assistant certificate, or
a fresh audit of the inherited C222/ZFC calibration.

## Material inspected and disposition

I read `graph_work/INDEPENDENT_REVIEW.md` and the graph sections of the main
`report.tex`: normalization, incidence energy, tree completion, opposite
occurrence pairing, alias quotients, the four-cycle example, the two-alias
quartic and its local optimality, and the exact off-zero lift identity.
The mathematical claims in that scope are valid under their stated and
checked partition/tree/normalization hypotheses. No new computation was
required; the first independent checker already verifies the literal data.

One exposition clarification was recommended to the author: explicitly
retain valid equality penalties at every surviving cardinality (the quartic
for size two, and at least two members for the selected unit path). The
author confirmed that the optional unit-alias-to-literal-one specialization
discussed in the first review was explored but accepted zero times in every
selected artifact; it is not an implementation step of these endpoints.
The clarification concerns completeness of exposition, not a counterexample
to the artifacts.

## Detailed checks

### 1. Normalization and tree flows

Triangular monic definitions of fixed constants and scaled source variables
give a unique integer-polynomial extension of every source tuple. Repeated
signed occurrences of the same logical half-constant correctly encode
doubling before collection. They need not be distinct logical monomials.

For fixed alias values, each internal tree edge occurs with coefficient
plus or minus one in the leaf equation. Eliminating leaves therefore gives
a unique integral flow. The final root equation is the block divergence
sum; it is the only remaining obstruction. This holds also for singleton
blocks. Distinct free coordinates and the spanning-tree condition are
essential and are explicitly covered by the checker.

The incidence energy has integral coefficients: edge-square contributions
occur at both ends, and off-diagonal products in each divergence square
have an even factor. Parallel prescribed edges do not change the argument.
Every summand in the final energy-plus-penalties expression is nonnegative
over the reals, so zero forces all divergences and penalties to vanish.

### 2. Pairing and quotienting

A prescribed edge directly between opposite row occurrences gives exactly
the same row balances as the two old hub edges; the removed hub balances
cancel. The literal row-block sums, rather than a possibly stale occurrence
table, are the correct invariant.

Identifying aliases of the same logical coordinate removes no zero, since
they already agree there. Copying the merged coordinate recovers the old
alias tuple. Rebuilding valid equality penalties preserves this zero
condition even though it generally changes the polynomial away from zeros.
The report correctly distinguishes this zero-set equivalence from a literal
whole-polynomial substitution identity. Normalization and tree uniqueness
upgrade the correspondence to a bijection with the original source zero set.

As an optional theoretical operation, specializing a unit alias to literal
one likewise removes no zero; the
inverse inserts one in that coordinate. After removing it from the unit
path, the remaining path must still enforce all its entries equal one.
Because the specialization can create lower-degree collisions with other
terms, the full collected polynomial must be checked again. The proof does
not rely on the old homogeneous-support separation afterward. This optional
operation is not used by the selected artifacts and no such specialization
implementation is claimed to be packaged.

### 3. The explicit four-cycle

For the directed cycle with labels ab, ad, cd, cb, the adjacent products are
a^2bd, acd^2, bc^2d and ab^2c, each with coefficient minus one. The four edge
squares have coefficient one. The two opposite products both equal abcd but
neither appears in the incidence energy. Thus the stated eight-term
height-one polynomial is correct and demonstrates precisely why a global
no-four-cycle restriction is stronger than necessary for this energy.

### 4. The quartic equality and its limited optimality

The factorization

    a^4+b^4-a^3b-ab^3=(a-b)^2(a^2+ab+b^2)

is exact. The second factor is positive except at (0,0), already on the
diagonal. The polynomial is consequently globally nonnegative and has
exactly the diagonal as its real zero set.

The degree lower bound is valid in the stated class. Odd total degree is
incompatible with global nonnegativity. A real-nonnegative quadratic
vanishing on the whole diagonal must be c(a-b)^2: in coordinates
u=a-b, v=b, any term u*(alpha*v+beta) would produce negative values.
An integer c>0 gives mixed coefficient -2c, violating height one.

The four-monomial lower bound is also valid in the stated class. Diagonal
vanishing makes the coefficient sum in each degree zero. Unit nonzero
coefficients therefore occur in even numbers in each occupied degree.
A nonzero polynomial with fewer than four terms must be the difference of
two distinct equal-degree monomials; its sign changes in the positive
quadrant as a/b crosses one. The argument correctly claims only a local
equality-gadget optimum, not global optimality of a consistency equation.

### 5. The off-zero lift

The canonical lift is a polynomial map: compute the unique normalizing
constants and scales, copy aliases, insert unit values, and solve tree
flows by integer additions and subtractions. Away from source zeros the
only nonzero divergences are block roots, carrying the original residuals
R_j and their negative total. All added defining rows and equality penalties
vanish under the lift. Hence, identically,

    P(L(z)) = [sum_j R_j(z)^2 + (sum_j R_j(z))^2]/2.

The right side is even an integer-coefficient polynomial after collecting,
equal to sum_j R_j^2 + sum_(j<k) R_j R_k. The report correctly avoids the
false simpler identity P(L(z))=sum_j R_j(z)^2.

## Boundary of this review

No claim is made here about the absence of zeros, Con(ZFC), optimality of
the search profiles, or the complete transitive arithmetic/logical source
calibration. Exact counts and coefficient lists rely on the independently
implemented literal checker and its artifact-specific receipts. This second
review verifies the mathematical implications connecting those checked
invariants, rather than repeating their computations.
