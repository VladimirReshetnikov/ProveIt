# Path from the checked finite kernel to the continuous iPRA development

## Formal status

The `.lean` files compile without unfinished proofs. Completed finite algebra,
compiling specification records, existing ProveIt proof objects, and future
continuous bridges are different deliverables. This roadmap does not assert
that a semantic Lean proof has automatically become an iPRA derivation.

## 1. Quote fixed programs

Translate each fixed `PR n` tree into the repository's primitive-recursive term
syntax. Composition stores a finite tuple of subtrees. Primitive recursion
has base arity `n`, step arity `n+2`, and input arity `n+1`, with argument
ordering `(time, previous, parameters)` in the step. Give fixed-tree graph
correctness by structural metatheoretic induction. Do not introduce a uniformly
primitive-recursive evaluator for arbitrary program codes.

The numeric encodings needed are signed integers as differences of naturals,
positive rationals as triples `(positive, negative, denominatorMinusOne)`,
finite lists with bounded lookup, and tuples. Every list traversal or search
must have a visible primitive-recursive bound. A term in Lean of type
`Nat → Nat` alone is insufficient evidence of primitive recursiveness.

## 2. Reuse object-language finite arithmetic

Use ProveIt's `FiniteKernel` and `Expectation` endpoints rather than translating
the semantic finite proofs from scratch. Quote each fixed weight and table
body as a `PTm`; clear all positive denominators; rewrite signed values using
positive/negative parts. For products and maximal estimates, reuse the
existing probability modules mapped in `README.md`.

If a finite assertion contains bounded quantifiers, compile them to bounded
Boolean folds. Induction is applied to the resulting quantifier-free
arithmetic invariant, with all other parameters held free. Never apply
quantifier-free induction directly to an unbounded assertion that a sequence
is Cauchy or that a completed-space limit exists.

## 3. Rational and event names

For rational codes `a=(a_num,a_den)` and `b=(b_num,b_den)`, `qClose k a b`
means exactly

```
abs(a_num * b_den - b_num * a_den) * 2^k ≤ a_den * b_den.
```

It is a finite decidable arithmetic predicate after the fixed generators have
been quoted. A regular name requires its universal closure for `k ≤ l`; this
universal closure is a hypothesis or a derived theorem, not an induction
formula.

For cylinder events at depths `d` and `e`, lift both to depth `D=max(d,e)`.
The prefix index at depth `d` of word `i < 2^D` is `i / 2^(D-d)`. The
symmetric-difference distance is the number of disagreeing table entries
divided by `2^D`. `RegularEventSpec.regular` is its cross-multiplied Cauchy
condition. Complete the following bridges:

1. Prefix refinement preserves cardinality after the expected power-of-two
   factor. This proves the probability and metric independent of chosen
   common depth.
2. Event Boolean operations are Lipschitz, with precision shifts when two
   approximation errors are added.
3. `event_mass_stability` descends probability to equivalent regular event
   names.
4. Event-name equivalence is represented by the explicit arbitrarily-small
   distance tests, without trying to decide real equality.

## 4. L1 observables and integration

Encode simple rational tables and common refinements. Clear their denominators
and invoke `expectation_stability` and `distance_triangle`. For a regular L1
name, the integral is the explicit rational sequence of finite integrals.
Its regularity follows from the finite inequality; no completeness axiom or
choice of an unspecified limit is needed. Prove positivity and linearity by
finite table algebra and explicit precision budgets.

For unbounded observables, attach tail-integral certificates. For a countable
union or a countable sum, attach a primitive-recursive tail modulus. Those
moduli are inputs or separately constructed programs, never outputs of an
unbounded search for convergence.

## 5. Continuous laws and analytic bridges

For each density constructor, quote its compact approximation program,
quadrature mesh selector, positive normalization bound, and tail selector.
Prove the finite rational error bounds first. Reuse the report's stability
estimate for normalization and explicitly account for each error in a target
precision. Normal-moment coefficient identities already in ProveIt do not
prove normalization or integrability of the Gaussian density; those are
separate analytic obligations.

## 6. Products and limit theorems

Finite product identities and maximal inequalities feed into finite precision
estimates on completed presentations. Lift them only after proving the
relevant event or ramp approximations and moment tails. Keep weak-law,
finite-window strong-law, and smooth-test CLT statements at their advertised
quantitative strengths. An unrestricted classical sigma algebra, automatic
conditional distributions, or an arbitrary no-modulus convergence theorem is
not a consequence of the completed finite kernel.

## Acceptance gates for a full formalization

- Each analytic evaluator has explicit PR syntax and finite correctness
  bounds, not only a semantic executable function.
- Each recursive proof invariant is quantifier-free after the advertised
  bounded-fold compilation.
- Every division comes with a positive lower-bound witness.
- Every limiting operation has a PR precision/tail selector and a proved
  finite error inequality.
- The final endpoints have actual `Prf PRAAx` types, with transitive
  dependencies and kernel checks recorded.
