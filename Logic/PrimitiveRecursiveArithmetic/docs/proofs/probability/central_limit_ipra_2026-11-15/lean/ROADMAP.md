# Lean and iPRA formalization roadmap

## Status boundary

The two `.lean` files are **uncompiled blueprints**, not a completed formalization. The preparation environment had no `lean`, `lake`, or `elan` executable. They contain no `sorry`, and they do not introduce a CLT axiom; instead they define records whose fields are the missing proof obligations. A completed project must define the actual semantic checker `beTest` and end with a value of `CentralLimitIPRAPlan.InternalProof beTest`.

The target ProveIt revision inspected for APIs is `979613af639a0e33b9d17b74af2a5629bb2d749f`; `lean-toolchain` pins `leanprover/lean4:v4.32.0`.

## Layer 1: exact finite probability

Create `CentralLimitIPRA/FinLaw.lean`.

1. Encode signed rationals by natural pairs with a positive denominator invariant.
2. Encode a finite law by a support length, value table, natural weights, and positive total weight.
3. Define exact finite expectation, CDF at a rational threshold, centered moments, products, and convolution.
4. Prove by finite sums:
   - mass is one;
   - expectation is linear;
   - product projections are independent;
   - means add and variances add for centered independent variables;
   - characteristic functions multiply.
5. Define mixed-radix enumeration of a product row. All recursors are primitive recursive.

These proofs should first be completed semantically in Lean over `Rat`, then mirrored as equations of `PR` syntax.

## Layer 2: regular names

Reuse the conventions in ProveIt's constructive calculus, Stirling, Taylor/Cauchy, and Bohr--Mollerup packets.

A regular name has rational endpoints `lo p`, `hi p`, nesting, and width at most `2^-p`. Implement:

- addition, multiplication on bounded intervals, reciprocal with a supplied positive margin;
- positive square root by rational bisection;
- range-reduced `sin`, `cos`, and `exp` by finite Taylor sums with explicit remainders;
- `pi` by a Machin formula and alternating arctangent sums;
- finite Riemann integration with a supplied derivative/Lipschitz bound;
- the Gaussian density and CDF, including Mills tail bounds;
- complex names as pairs of regular names.

Every evaluator must have a fixed primitive-recursive precision schedule. Avoid a universal evaluator for arbitrary programs.

## Layer 3: analytic lemmas

Implement the manuscript's finite certificates in this order.

1. Taylor inequalities:
   - `|exp(i x) - 1 - i x + x^2/2| <= |x|^3/6`;
   - `0 <= exp(-x) - 1 + x <= x^2/2` for `x >= 0`;
   - `1 - cos x >= x^2/3` for `|x| <= 1`.
2. Gaussian integral recurrences and the rational bounds `25/8 < pi < 16/5`.
3. The kernel `v_T(x) = (1-cos(Tx))/(pi*T*x^2)`, with its removable value at zero, normalization, triangular Fourier transform, and tail mass `<= 4/(pi*T*h)`.
4. Constructive Esseen smoothing with constant `24`.
5. The damping lemma using an independent copy:
   `1 - |phi_j(t)|^2 = E(1-cos(t(Y_j-Y'_j)))`.
6. Finite product telescoping.

All improper integrals are represented by finite cutoffs plus explicit tails. No appeal to monotone convergence, dominated convergence, or countable choice is required.

## Layer 4: core CLT proofs

Implement two theorems.

### Bounded array

For centered independent finite laws with total variance one and `|Y_j| <= b`, prove pointwise for every rational threshold

`|F(q) - Phi(q)| <= min 1 (7*b)`.

The only induction over the number of summands uses the product telescoping identity; fix `q`, `t`, and all precision parameters before induction.

### Berry--Esseen

Let `beta = sum E|Y_j|^3`. Prove

`|F(q) - Phi(q)| <= min 1 (64*beta)`.

For `beta < 1/64`, use `T=1/(16*beta)`, the truncated second-moment damping quantities `q_j`, and the manuscript's rational constant audit. For larger `beta`, use the trivial bound one.

## Layer 5: QF object-language reconstruction

1. Compile every bounded loop and rational operation to `PR` syntax.
2. Define `berryEsseenFiniteTest(row,q,p)` so that invalid row codes return zero and valid codes check a slackened dyadic interval inequality.
3. Prove the defining equations of the checker in `PRAAx`.
4. Re-run the analytic proof with all precision and length parameters fixed before induction. The open invariant is an equation/inequality of coded integers and is QF.
5. Construct `Representation`, then the much stronger `InternalProof`.
6. Apply `closeProof` and `nativeProof` from `ObjectLanguageTarget.lean`.
7. Audit with `#print axioms`; the intended internal theorem should not depend on semantic reflection.

## Layer 6: corollaries

After the core theorem is internal, add separate modules for:

- iid sample means and the explicit `64*rho/(sigma^3*sqrt n)` modulus;
- quantitative Lindeberg truncation and Lyapunov;
- binomial/de Moivre--Laplace, reusing the Stirling packet;
- rational projections and fixed-dimensional smoothing;
- random sums;
- bounded finite-range dependence;
- finite-tree martingales;
- lattice local limits;
- products via logarithms.

The ordinary `Real`/measure-theoretic interpretation should remain downstream. It is useful for matching textbook notation, but it must not replace the internal `PRAAx` derivation.
