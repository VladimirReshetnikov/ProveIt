# Remaining formalization, with explicit proof boundaries

## 1. Concrete coding layer

Implement a fixed primitive-recursive pairing/list encoding and signed
rationals `(sign, numerator, denominatorMinusOne)`. Rational equality and
ordering can be checked by cross multiplication; canonical reduction is
not needed for the mathematical identities. Prove the `RationalCodes`
fields of `Blueprint.lean`, including the comparison convention that
returns natural number `1` exactly when the inequality holds.

For each arithmetic operation, retain a finite iPRA derivation using its
defining equations. Do not infer this from the mere existence of a Lean
function or from the totality of `PRCode.eval`.

## 2. Reverse weights and certificate checking

Represent a finite directed acyclic computation graph in topological order.
Code rational matrix entries and a sink vector. Process vertices from last
to first, setting `W[u] = b[u] + sum_{v>u} W[v]*L[v,u]`. The reverse-loop
invariant states that every processed column already satisfies its exact
balance and that the unprocessed state equals the accumulated contributions
from the processed vertices. It is a finite conjunction coded by a bounded
Boolean scan.

Prove primitive recursiveness of the producer and its rational bit bounds.
Then instantiate `weighted_budget`. For cyclic data, a supplied nonnegative
supersolution is checked by bounded rational comparisons and fed to
`weighted_budget_supersolution`; existence is not assumed.

## 3. Completion and modulated maps

Use `MetricData`, `MetricLaws`, `Name`, `RegularName`, and
`EqualitySchedule`. The `RegularName` condition is the finite two-index
inequality `d(x_m,x_n) ≤ epsilon(m)+epsilon(n)`.

Prove finite triangle estimates and separation with rational slack. Replace
an arbitrary supplied modulus by its finite prefix maximum when monotonicity
is needed. Construct the image name by evaluating the map at a sufficiently
accurate input stage. Every requested precision has a PR-selected finite
stage. Prove equality preservation and uniqueness through these inequalities.
Only then introduce a setoid completion in Lean; that setoid belongs to
metatheory and does not become an internal domain of arbitrary sequences.

## 4. Effective compactness and formula semantics

Use `FiniteNetData` for explicitly supplied nonempty nets. Implement a
bounded scan over every net, using the verified `argminQ` theorem after
decoding the rational table. Obtain finite maximum analogously by negation.

Define term evaluation and atom moduli for a fixed signature and environment.
Interpret `ContinuousFormula` by structural recursion, with a rational
precision request at every node. The `oneMinus` and `truncatedSub`
connectives have explicit error bounds. At quantifier nodes combine the
formula modulus on the supplied net with `finite_minimum_stability`; budget
the local approximation errors by the checked weighted verifier. Prove the
result by external induction on the fixed formula and then compile each
fixed case. This does not produce arbitrary exact models or an infinitary
compactness theorem.

## 5. Measure and L1

Implement finite disjoint partitions, their common-refinement algorithm,
rational cell weights, and the refinement identities for measure. The
`SimpleData` integral and L1 norm are explicitly finite weighted sums.

Prove the scalar absolute-value triangle inequality by decidable sign
cases, lift it by `sumQ_mono`, and prove the finite integral bound
`abs(integral s) ≤ l1norm s`. Establish independence under common
refinement. Use the completion construction from step 3 for L1 names.
Finite Fubini is `sumQ_exchange`; passing to completion requires the
separately proved L1 Lipschitz estimate.

For the effective Vitali theorem, prove the scalar clipped-value estimate,
then sum over the good and bad cells. Its bound contains the supplied tail
budget, convergence-in-measure schedule, truncation bound, and total mass.
Add approximation errors before accepting the final certificate. A
dominating function alone is not an algorithm for those schedules.

## 6. Normed algebra and topology

Instantiate the abstract ring with a concretely coded algebra and prove the
norm axioms through finite rational inequalities. `geometric_left` and
`geometric_right` already supply the exact finite inverse residual. The
remaining analytic work is a finite-tail norm estimate with an explicit
geometric contraction schedule, followed by the completion theorem.

For a square-zero differential `D` and candidate homotopy `h`, the exact
finite identity is already `correctedContraction_residual`. Prove the
displayed norm estimates in the paper and use them to build a regular
name for the corrected homotopy. No unbounded search for a spectral gap
is permitted; the contraction margin is input data.

For analytic functional calculus, a coded coefficient stream and a supplied
`MajorantTail` are the core inputs. Prove Horner or doubling evaluation
identities in the abstract ring, then quantitative norm propagation. The
majorant is checked for arbitrary finite tails; no actual infinite sum is
needed in the arithmetic kernel.

## 7. The actual iPRA interpretation theorem

Reuse ProveIt's existing ConciseIPRA first-order syntax, `Prf PRAAx`
derivation constructors, and checked bounded-syntax and arithmetic libraries.
There is no need to build a competing proof checker. Construct (a) object
derivations for each fixed PR definition, (b) the
finite loop invariants using quantifier-free induction, and (c) translation
of each allowed analytic construction into a fixed family of finite
certificates. The metatheorem must explain its handling of assumptions,
substitution, and parameters. It must not quantify over all PR programs and
then silently use a uniformly PR evaluator.

The current package supplies human arguments, finite checked mathematical
kernels and typed specifications. This final translation into existing
object-theory derivations remains a formalization task, not an established machine
checked theorem.
