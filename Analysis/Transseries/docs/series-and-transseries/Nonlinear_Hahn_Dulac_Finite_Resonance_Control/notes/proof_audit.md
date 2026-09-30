# Proof and hypothesis audit

## Main chain

Finite additive antidiagonals imply finite divisor sets. Positive minimum action
delta makes every nonlinear coefficient depend on strictly smaller actions,
with a valuation gain of at least delta in fixed-point differences. The
polynomial Euler solver supplies a normalized solution at every action.

The coarse degree budget is
`h(gamma) = floor(gamma/delta) * sum_{lambda<=gamma} s_lambda`.
At a resonance lambda, the source degree is at most `h(lambda)-s_lambda`.
This margin is needed: the resonant inverse does not preserve the unrestricted
same-degree polynomial space.

For the exact slope, the actual resonant polynomial blocks provide the upper
bound at resonances. At any other action, multiplication takes weighted averages
of prior degree/action ratios and the Euler solver does not increase degree.
Well-founded induction gives the exact finite maximum, including cancellations.

Divisor-closed ancestry makes all determining resonant blocks polynomial in
finitely many input coordinates, for fixed matrix and exponent data. Algebraic
sublevel strata follow by vanishing of finitely many high-degree coefficients.
Logarithm-free invertible coordinate changes cannot increase the slope; their
logarithm-free inverse proves equality.

The analytic proof uses a weighted coefficient l1 Banach space with the coarse
degree budget. Large-action Euler inversion offsets the linear degree growth.
The nonresonant gap bounds inverses at bounded actions. Resonant integration is
bounded on the restricted source space. Explicit majorants give a contraction.
Evaluation and differentiation follow from absolute coefficient estimates.

Gap failure is necessarily left accumulation at a positive eigenvalue. The
forcing coefficients epsilon_n/n at distances epsilon_n from the eigenvalue
produce solution coefficients -1/n at bounded actions. This gives arbitrarily
small, logarithm-free counterexamples to universal absolute realization.

In the nonlinear accumulation family, the entire block through action 2 is
explicit. It is summable precisely when sum n|t_n| is finite. After subtracting
that infinite block, all remaining actions are at least 5/2. A bounded
nonresonant tail inverse and a quadratic contraction establish sufficiency.

## Boundaries that must not be dropped

- Gamma is a nontrivial well-ordered additive submonoid of nonnegative REAL
  actions. Higher-rank ordered groups require a separate argument.
- The source coefficients have no logarithms, and no derivatives of y occur
  inside F. Both restrictions are used.
- The constant and linear action-zero terms of F vanish. The whole constant
  linear operator is in A, whose spectrum is real; Jordan blocks are allowed.
- The normalized solution has positive actions in the specified monoid. It is
  not a classification of every possible transseries solution of the ODE.
- The exact slope uses polynomial block degrees, with zero and constants
  contributing zero. It is not a tail limsup or an exact convergence radius.
- The inverse coordinate change has invertible CONSTANT linear part. Singular
  shears, variable changes in x, and logarithmic changes are excluded.
- Polynomial dependence is asserted for the determining blocks, not for the
  discontinuous degree/slope statistic itself.
- Finite divisor data can be mathematically finite without being effectively
  discoverable from an arbitrary input presentation.
- The gap criterion is necessary for the UNIVERSAL convergence property over
  all inputs on the whole monoid. It is not necessary for each individual F.
- Absolute coefficient convergence is stronger than arbitrary conditional or
  renormalized summation. No assertion excludes all analytic solutions in
  divergent examples.
- An action cutoff need not contain finitely many lower blocks. Whole infinite
  blocks require separate summation or certified representation.

## Verification status

All general claims are supported by conventional proofs in the LaTeX article.
The accompanying program checks finite exact identities and floating-point
illustrations only. It does not prove the infinite-support theorems and is not
a Lean development. Numerical checks are not interval arithmetic. The source
uses assertions, and the main routine explicitly rejects Python -O mode.

Classical support, fixed-point, and Dulac majorant ingredients are acknowledged.
Historical novelty was investigated through selected repository and primary
literature sources, not established by an exhaustive search or independent
peer review.
