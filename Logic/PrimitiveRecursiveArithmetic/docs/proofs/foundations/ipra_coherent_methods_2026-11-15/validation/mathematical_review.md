# Mathematical review and limits of the checks

The final report and the principal application targets were cross-checked by
separate review passes. This is a review record, not a claim of independent
machine verification of the human mathematics.

## Corrections incorporated before release

- The bounded existential scan uses its current scan length as the failure
  sentinel, so its stage invariant is valid before the final bound is reached.
- The uniqueness induction for lifting explicitly treats the step from
  filtration zero to filtration one using the selected seed class.
- The Hurwitz Leibniz identity truncates the undifferentiated factors to
  the output precision, and differentiation requests one extra coefficient.
- The ODE construction states exactly which coefficient prefix it consumes.
- Finite uniqueness specifications explicitly include validity.
- Homomorphisms in arithmetic instances are fixed PR maps with supplied
  preservation laws.
- The Cauchy-name counterexample labels the assertion that every represented
  value is rational as an external classical metatheoretic statement.

## Lifting and Hurwitz review

The review checked the finite Taylor remainder, Jacobian congruence, both
inverse orientations, the N-1 iteration bound including N=1, uniqueness in
the seed class, projection compatibility, and the composite-modulus
filtration. No remaining mathematical error was identified.

The right inverse congruence is used for residual improvement; the left
inverse congruence is used for uniqueness. The fixed inverse gives linear
precision gain, and the stated sharp example has residual (-q)^(r+1).

The Hurwitz identities remain valid in arbitrary characteristic because
binomial coefficients act by repeated addition. The ordinary time element
T has T^(*r) equal to r! in slot r, so the report does not identify its powers
with an ordinary monomial basis without the needed factorial factors.
The concrete Lean ODE target has the narrower scalar rational scope stated
in the formalization documentation.

## Weighted norm review

The review checked the change of basis and rescaling identity, the sign of
the leading coefficient, the Vandermonde row determinant, repeated-fiber
divisibility, successive removal of distinct-coordinate factors, the sharp
zero count, the eventual dimension threshold, and the adjugate construction.
No remaining mathematical error was identified.

The concrete Lean targets match the report's positivity, coprimality,
nonzero coefficient, strict lower-weight, reduced-degree, and nonzero-G
hypotheses. The natural-number threshold m*d-m-d represents
max(0,md-m-d). Monic reduction has sufficient fuel because every active step
strictly lowers the highest remaining Y-degree.

`FiberPowerGoal` is also stated when G=0; that strengthening is valid because
the zero polynomial is divisible by every polynomial. The existential
quotient in the host definition of divisibility is a conclusion. The
arithmetic proof computes and carries that quotient in a bounded invariant,
so it does not require induction on an unbounded existential formula.

## Logical status

The review found no hidden countable-choice, universal-PR-evaluator, or
reflection assumption in the stated human proof architecture. The report
separates host Lean theorems, embedded derivation constructions, compiled
unproved propositions, and finite executable checks.

The full embedded derivations of the universal application theorems were
not constructed. The approximation-cover and global height/list obligations
were not resolved. The contribution is stated relative to the inspected
repository packets and makes no mathematical-literature priority claim.
