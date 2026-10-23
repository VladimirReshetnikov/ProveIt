# Independent audit of support-sensitive coefficient extraction

Inspected `../packing/SUPPORT_PROOF.md`, its LaTeX companion,
the two literal parent circuits, the weight data, source builders, and the
finite-support verifier at baseline ProveIt commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`.

## Mathematical verdict

The weaker isolation condition is sufficient. No local mathematical
defect was found in its application to either finalizer.

1. The protected set contains every nonzero quadratic source monomial
   after all positive parent coordinates are translated by one. Each
   protected alpha is checked against **all** 528 quadratic monomials,
   including absent monomials, not just the other protected monomials.
   This is the condition actually needed for target extraction.
2. Cross-row contamination is excluded by the target separation 381,
   greater than the largest possible difference of monomial exponents,
   380. Within a row, the protected exponent is unique. The factorial
   normalization then gives exactly twice each quadratic residual.
3. Every D coefficient occupies a different position, across and within
   rows. Therefore its coefficient bound is unchanged. For the product
   C_z D, collisions among unprotected expansion monomials cause no
   problem: the convolution estimate uses the full sum of absolute
   coefficients `(1+sum |z_i|)^2`. It does not require those expansion
   monomials to have distinct exponents and adds no factor for 22 rows.
4. These are exactly the hypotheses used in the retained no-carry
   arguments. Positivity of D comes from its unchanged leading
   coefficient 2. The low mask recovers the positional digit form of g
   before the source residuals are interpreted. The bound includes all
   off-target collisions, so malformed g or hidden carries are not
   being assumed away.
5. The Sun source uses the 65-operation parent; the Jones source uses
   the 60-operation parent. The supplied verifier checks the complete
   symbolic relation `z_old=z_new+1`, with the coefficient ports still
   symbolic, and checks the two sets of normalized rows independently.
   Their supports agree, but their coefficients have not been identified
   erroneously. The positive inverse shift is an inherited semantic
   fact, explicitly retained in `PARENT_TRANSPORT_SHIFT.md`.
6. Replacing the weights does not change the complete fixed compiler
   tuple. The final source builders use maximum weight 190, rather
   than wrongly taking the last unsorted weight (144) as the maximum.
   Their target origins differ by one, as in the two inherited sources;
   both coincide with their emitted coefficients.
7. The nine-variable cancellation certificate retains the exact general
   identities required for its smaller degree. The direct circuit and
   certificate circuit are distinguished in operation counts. The
   ten-variable degree is certified by a nonzero coefficient at a
   propagated total-degree upper bound, not by a numerical fit.

## Finite evidence checked

The supplied support certificate records 71 protected monomials, 136
source terms, 278 distinct sums among 528 possible pairs, and 71,808
source/expansion comparisons with exactly 136 diagonal target hits.
The proof explicitly permits the remaining 250 pair-sum repetitions.

The proof's degree and operation metrics agree with the supplied
receipts: 9 positive coordinates, degree 30,947,584, 651 operations;
9 nonnegative coordinates, same degree, 654 operations; 10 unrestricted
integer coordinates, degree 56,593,864, 653 operations.

## Scope

The review establishes the new extraction transformation and its
interface to the inherited carry proofs. The native compiler, K215
calibration, Jones ratio theorem, and Sun ten-integer theorem remain
the stated mathematical dependencies. This is not an end-to-end
formal proof, a proof of consistency, or a claim of global optimality.
