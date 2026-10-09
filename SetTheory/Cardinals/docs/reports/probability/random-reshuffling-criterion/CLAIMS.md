# Claim and verification boundaries

## Proved in the article

- Exact equivalence: eventual one-block, all-initial-state Euclidean Gram ordering
  holds iff the mean Hessian preserves the kernel of the matrix variance.
- The same criterion for every fixed positive position schedule and every
  fixed block length between two and the sample size.
- Exact fourth-order smallest-eigenvalue coefficient in the failure branch;
  explicit affine-in-step adverse witnesses.
- Rank-one component Hessians always satisfy the criterion; the conclusion
  survives a common scalar shift. A common minimizer is required for the stated
  optimization interpretation.
- Rank two and dimension two already permit a strictly convex obstruction.
- Exact two-component Euclidean and objective-loss gap identities.
- A general second-order metric coefficient and a fixed-state objective reversal
  under the kernel leakage condition.
- Local nonlinear persistence with the order of quantifiers stated in the paper.
- Conservative explicit rational step intervals and a polynomial-time exact
  classification procedure on rational inputs.

## Proof dependencies

The constant-step classification uses only elementary finite sampling identities,
linear algebra, polynomial expansion, and a self-contained perturbation lemma.
The arbitrary-weight extension additionally uses the complete degree-six
integer-coefficient identity printed in the appendix. The support-size lifting
argument proves this identity for arbitrary block length from the finite table.
No unverified theorem from `openai/math` is a dependency.

## Computationally checked

The delivered `results/verification.json` reports 1,291 exact assertions.
Expectation matrices are computed by rational sandwich recursion and checked
against independent path enumeration on six fixtures. The weighted polynomial
identity is checked by symbolic integer arithmetic. Explicit interval claims
come from proofs, not solely from the sampled rational step values.

The minimal example checker is independent of the main matrix code and uses the
Python standard library. Its CSV also contains high-precision decimal eigenvalue
displays, which are not used as proof assertions.

## Not claimed

- Historical first discovery, peer review, or proof-assistant formalization.
- Resolution of the original Recht-Re noncommutative AGM conjectures, whose
  general forms already have published counterexamples.
- A contradiction to convergence-rate comparison results, including Liu (2026).
- A new asymptotic convergence rate or runtime improvement for SGD itself.
- Automatic extension from one block to multiple epochs, from Euclidean error to
  every metric, or from common-minimizer quadratics to general noisy objectives.
- Uniform asymptotics when n, m, dimension, condition numbers, or schedule ratios
  vary with the small step parameter.
- Numerical-rank robustness without a separate certified perturbation analysis.

The proposed contribution for independent mathematical and bibliographic review
is the exact classification, its coefficient, and the constructive consequences,
not the already-known observation that reshuffling can sometimes perform worse.
