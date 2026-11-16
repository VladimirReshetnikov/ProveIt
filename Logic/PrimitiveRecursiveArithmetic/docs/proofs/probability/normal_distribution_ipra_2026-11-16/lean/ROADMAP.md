# Roadmap to a complete Lean and object-iPRA formalization

## 1. Representation layer

Implement signed integers, positive-denominator rationals, dyadics, finite lists, tuples, and closed intervals as natural-number codes. Prove cross-multiplied equality/order, interval arithmetic, powers, absolute values, finite sums/products, and bounded minimization. Reuse IPRADerivations wherever the required symbol already exists.

Every externally fixed evaluator must be represented by a concrete `PR k` term. Do not add a universal evaluator for arbitrary primitive-recursive source code.

## 2. Exact polynomial layer

Formalize coefficient arrays and finite polynomial operations. Prove:

- the moment recurrence `m_(n+2)=(n+1)m_n`, with `m_0=1`, `m_1=0`;
- `m_(2r)=(2r-1)!!` and `m_(2r+1)=0`;
- `He_(n+1)=x He_n-n He_(n-1)`;
- derivative and coefficient recurrences;
- finite Wick pairing enumeration for any externally fixed order.

These are bounded identities and should be the first actual `Prf PRAAx` milestones.

## 3. Certified constants and elementary functions

Compile the algorithms mirrored in `code/gaussian_certificates.py`:

1. `sqrtInterval(q,p)` by bounded dyadic bisection;
2. `atanPartial` and Machin's identity for a `piInterval(p)`;
3. `expNegInterval(q,p)` by range reduction and alternating Taylor sums;
4. multiplication, inversion, and square-root interval propagation.

For each producer define a Boolean checker and prove soundness in `Prf PRAAx`. The object formula contains only codes, equations, and rational inequalities.

## 4. Finite integration and tails

Port the existing calculus packet's Riemann-sum interface. For Gaussian integrands prove a primitive-recursive tail cutoff using, for example,

```text
x ≥ T ≥ 1  ==>  exp(-x^2/2) ≤ exp(-x/2),
```

and geometric/exponential tail estimates. Formalize integration by parts first on a finite interval, then discharge boundary terms and tails using explicit inequalities.

Key endpoints:

- Gaussian normalization;
- moment integration by parts;
- Mills inequalities and finite asymptotic expansion;
- the derivative identity for the Gaussian Fourier transform.

## 5. CDF and quantiles

Define two independent CDF producers:

- integrated alternating Taylor series;
- density-factor series with a finite recurrence.

Prove interval soundness and width bounds. Define `quantileBracket(p,q)` by bounded bisection on a precomputed tail bracket. The theorem is interval-valued: it does not decide equality of arbitrary real names.

The first high-value closed theorem should certify the six rational enclosures for `P(|Z|≤n)`, `n=1,…,6`.

## 6. Probability-law interface

Represent a law by a fixed density/CDF name and explicit nonnegativity, normalization, tail, and continuity contracts. Expectations of represented functions are certified integrals. Independence is a product presentation, not a second-order predicate over arbitrary measures.

Prove affine transport and convolution closure by completion of squares or characteristic functions. For multivariate normals, encode rational symmetric matrices and positive-definiteness through an explicit Cholesky/LDL certificate with lower pivots bounded away from zero.

## 7. Information and sampling theory

Once logarithm and gamma/beta contracts are available, formalize:

- entropy, KL, Hellinger, and Fisher formulas;
- orthogonal sample decomposition using exact rational matrix identities plus a certified orthogonal completion;
- chi-square, t, and F change-of-variable formulas;
- MLE polynomial identities and the identical-data boundary case.

Maximum entropy requires a represented density with explicit integrability for `p log p`; state that boundary data in the theorem rather than appealing to classical existence.

## 8. Object-language compilation

For each theorem family:

1. write a closed formula `φ : Fm PTm 0`;
2. define every numerical operation as a concrete `PR k` symbol;
3. prove defining equations;
4. derive loop invariants by `PRA.qfInd`;
5. compose the derivation using `Prf` rules;
6. export a theorem of type `([] : List (Fm PTm 0)) ⊢[PRAAx] φ`;
7. transport it with `pra_iff_native`.

A metatheoretic theorem about `Nat`, `Rat`, or `Real` is useful for finding the proof but is not the endpoint.

## 9. Suggested module order

```text
Gaussian/Codes.lean
Gaussian/Intervals.lean
Gaussian/FiniteSums.lean
Gaussian/Polynomials.lean
Gaussian/Moments.lean
Gaussian/Hermite.lean
Gaussian/Sqrt.lean
Gaussian/Pi.lean
Gaussian/Exp.lean
Gaussian/Quadrature.lean
Gaussian/Tails.lean
Gaussian/CDF.lean
Gaussian/Quantile.lean
Gaussian/Transforms.lean
Gaussian/Laws.lean
Gaussian/Information.lean
Gaussian/Statistics.lean
Gaussian/ObjectTheory.lean
Gaussian/NativeExport.lean
```

## 10. Completion audit

CI should reject `sorry`, `admit`, and new axioms; print the axioms of ambient helper theorems; and verify that every headline export literally contains `Prf PRAAx`. The exact-rational Python fixtures may be imported as test vectors, but Lean must prove the universal checker-soundness theorem independently of those examples.
