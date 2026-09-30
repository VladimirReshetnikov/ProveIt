# Proof audit

## Scope

The system is D Y = (Lambda + A) Y, D = x d/dx. Lambda is a constant
real diagonal matrix. The nonzero entries allowed in A follow a fixed
finite acyclic directed graph, permuted into strictly upper-triangular
form. Each edge has a fixed positive well-ordered real exponent support.
Different scalar edge coefficient families vary independently.

No local finiteness assumption is made. Accumulating sets such as
{1 - 1/n : n >= 2} are permitted. The supports need not be finitely generated.
The conclusions concern absolute coefficient convergence, not conditional
summation or all possible analytic realizations.

## The proof's essential steps

1. **Finite path fibers.** Two well-ordered real sets have well-ordered sum
   and finitely many decompositions of a fixed exponent. Induction along a
   finite path supplies finite coefficient sums. There are finitely many
   paths. This is a support argument, not an assumption that bounded
   supports are finite.

2. **Exact resonances.** The polynomial inverse of beta + d/dL uses a finite
   geometric derivative sum for beta != 0, and zero-constant integration
   for beta = 0. A path kernel's log degree counts the zero suffix factors;
   its top divided-power coefficient is the product of the reciprocals of
   all nonzero suffix factors. It is never zero.

3. **Weighted necessity.** Unbounded finite examples alone do not prove the
   existence of a divergent infinite input. Isolating one chain gives a
   multilinear map on fixed-support Banach spaces. Coordinatewise finiteness
   gives a separately closed graph; the closed graph theorem and uniform
   boundedness give a joint bound. Atomic inputs then identify the exact
   operator norm. This supplies the required universal quantifier.

4. **Gap necessity.** On tuples whose positive total exponents approach a
   finite endpoint spectral difference, all suffix exponents remain bounded.
   The top divided-power coefficient forces kernel blowup when the full-path
   denominator tends to zero. Exact zero suffix denominators are omitted
   from the product, not divided by.

5. **Gap sufficiency.** Every suffix is itself an allowed path. The finite
   collection of positive nonresonant path gaps therefore bounds every
   inverse in every path kernel. Finite path length bounds total growth.

6. **All radii.** The bad witnessing exponents can be restricted to a bounded
   interval. On bounded exponent intervals, all positive radius weights are
   mutually comparable. The isolated path contribution remains divergent
   after any nonzero scalar rescaling of its edge inputs.

7. **Two normalizations.** H is a polynomial-logarithmic Frobenius factor;
   P is a log-free normalized gauge. They are not identified. Their
   fundamental matrices differ by a constant matrix because the constants
   of the differential ring K[L] are exactly C. Multiplication by finite
   monomial-log factors preserves absolute coefficient membership, proving
   the equivalence. The path operator's exact norm is not asserted to equal
   the norm of P.

8. **Stable chain realization.** The entire integral kernel groups the
   resonant constant and the canonical block before summation. The two
   pieces must not be separately summed when their moments diverge.
   Bounded exponent data and l1 coefficients justify locally uniform
   analytic summation. A direct exponential estimate proves every fixed
   formal-prefix asymptotic statement.

9. **Crossover.** After scaling, the grouped tail is a left Riemann sum of
   a positive decreasing convex function. Rectangle bounds and the exact
   trapezoidal-error identity prove the two-sided certificates. No exchange
   with a divergent ungrouped canonical sum occurs.

## Important boundaries

- The unrestricted-support normed Hahn algebra is NOT declared complete.
  Functional analysis uses fixed well-ordered support spaces.
- Positivity and real order are used in the small-divisor necessity proof.
- Independence of edge coefficients is necessary for the universal graph
  criterion. The four-dimensional cancellation example demonstrates why a
  graph alone does not classify correlated matrix directions.
- Acyclicity bounds word length. General matrix cycles are not covered.
- A fixed nonzero nilpotent constant term is not silently treated as an
  independently variable positive-exponent edge.
- The analytic solution of a differential equation can exist when its
  normalized Hahn gauge diverges. These are different assertions.
- The stable realization is basepoint-selected and proved for the chain;
  no multiplicative summation map on the full Hahn field is claimed.
- Finite symbolic verification and high-precision numerical checks are not
  Lean proofs or independent peer review.

## Relationship to prior work

The predecessor's whole-semigroup gap theorem and finite resonance ancestry
are acknowledged. The new target is its explicitly posed smaller-support,
restricted-matrix-direction question, with an exact independent weighted
refinement. The Frobenius normal-form architecture, finite polynomial inverse,
and general support machinery are not represented as new discoveries.
A targeted literature check is not sufficient to establish worldwide priority.
