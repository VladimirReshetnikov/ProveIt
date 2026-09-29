# Proof audit and scope

## Essential hypotheses

The scalar coefficients and monomial exponents are real. The monomial group
has finite logarithmic depth and lexicographic dominance, with x the outer
variable. Supports are reverse well-ordered. The Euler perturbation theorems
require n >= 1 and one uniform real epsilon > 0 such that all perturbing
coefficient blocks have outer x-exponent <= -epsilon.

Smallness only in log(x) does NOT satisfy this hypothesis. No arbitrary
analytic evaluation of formal Hahn series is assumed. Nonreal roots of P do
not contribute real-power homogeneous modes; no oscillatory extension is
silently included. A constant nonzero polynomial P is allowed.

## Dependency chain

1. Finite support shifts give a strong derivation and Leibniz rule.
2. Inside a block, each lower derivative lowers the L-exponent by one.
   This justifies formal power-series functional calculus in that derivative.
3. Recursive integration yields a single deepest-log residue defect and
   constants as the derivative kernel.
4. Integration by parts gives the necessary moment conditions; the explicit
   Green formula proves their sufficiency and the one-log repeated-primitive
   formula. Independent witnesses prove cokernel dimension.
5. Real-root blocks of P(E) are split with explicit residue moments, kernel
   coordinates, and a normalized generalized inverse G. Nonresonant blocks
   are inverted by the formal derivative functional calculus.
6. GR strictly lowers the x-exponent. Its geometric series is strongly
   summable. Applying G and the residue projection yields exactly Mc = b(f).
7. The matrix cutoff follows from the root spread and the support decrease.
   It bounds perturbation depth, not runtime on arbitrary noncomputable input.
8. After adjoining one log T, resonant block inverses raise T-degree by at
   most one independently of multiplicity. Strictly descending x-exponents
   allow each distinct root to be visited at most once.
9. Every homogeneous solution in the entire next-depth Hahn field is spanned
   by the constructed polynomial-in-T solutions: remove its highest root
   block successively. This is needed for the sharpness statement about ALL
   next-depth solutions, not only the specifically constructed ones.
10. The sharp family has GJ=0 on each first resonant transfer, making its
    matrix exactly a Jordan shift, not merely a first-order approximation.
11. The analytic example is independent: a genuine Volterra norm contraction
    constructs two solutions, while the Laplace block has an exact signed
    remainder. Only the decisive first outer block is matched explicitly.

## Potential overclaims deliberately excluded

- An exhaustive literature-priority claim.
- A Lean verification or repository build of the new theorems.
- An algorithm for arbitrary uncomputable Hahn inputs.
- A general analytic realization or summability theorem.
- Equating support truncation bounds with real numerical error bounds.
- Preserving all fixed-depth homogeneous solutions under outer-small
  perturbations: the sharp family explicitly disproves that claim.
- A bound on the new-logarithm degree independent of distinct resonances.
- A theorem for perturbations only small in a deeper logarithmic coordinate.

## Computational evidence

The supplied tests use finite rational blocks with a guard cutoff and exact
finite matrices. They check identities, signs, root multiplicities and
selected sharpness cases. They are supplemental evidence, not proofs of the
infinite-support or general mathematical statements.
