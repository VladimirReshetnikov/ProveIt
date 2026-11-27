# Lean integration roadmap (not implemented or kernel-checked)

## 1. Source interface

The companion `PrimeCodeInput.lean` is a small import adapter written against the exact exported names in `grh/src/Main.lean`. It contains no proof of the new results. To test it, place a copy at the root of the vendored `grh` Lake project (not the ProveIt root), build that project's dependencies and run `lake env lean PrimeCodeInput.lean`. The intended Lean 4.35.0 / Mathlib commit is in the vendor README. This command has not been executed here; Lean is unavailable locally.

## 2. Suggested module decomposition

| Module | Statement to formalize | Dependencies |
|---|---|---|
| `PrimeCodes.Window` | Polynomial window law and uniform character bias; maximum atom | Real/complex analysis, primes, von Mangoldt, Mellin inversion, explicit formula, GRH input |
| `PrimeCodes.BinaryFourier` | Indicator of affine subspace equals normalized sum of characters of orthogonal complement | Finite vector spaces over `ZMod 2`; character orthogonality |
| `PrimeCodes.Rectangle` | Probability of rank deficit at least h bounded by `2^r * 3^n * (2^-h + eps)^h` | Conditional expectation on finite distributions; rank/span; union bounds |
| `PrimeCodes.Reciprocity` | Nonzero row subset gives a primitive quadratic character; nonzero column subset gives positive fundamental discriminant character | CRT, Legendre/Jacobi/Kronecker symbols, quadratic reciprocity |
| `PrimeCodes.Finite` | Finite two-sided failure bound (Proposition 3.3 of the report) | Above; binomial counting; collision bound |
| `PrimeCodes.Asymptotic` | Both main asymptotic theorems | Entropy inequality, PNT, asymptotic comparisons |
| `PrimeCodes.Prefix` | Reverse exclusion of short dependencies and long-relation sum | Same window lemma, Fourier convolution, asymptotics |

## 3. Definition choices

- `Bit := ZMod 2`. `A : Matrix (Fin r) (Fin n) Bit` with entry `0` or `1` depending on the Legendre symbol of `p j` modulo `q i`.
- Distinctness is `Function.Injective q` and `Function.Injective p`; disjointness is `∀ i j, q i ≠ p j`; primality and oddness explicit.
- Represent a code as the image of the linear map `u ↦ u A`; its dual as the kernel of `v ↦ A v`. To avoid minimum of an empty set, state distance via the universal nonzero weight inequality. Include the stronger `∀ u ≠ 0, weight (u A) ≥ a` to ensure full rank.
- Define rectangle rank by restricting row/column index types to finite subsets, and applying dimension of the column span. Rank-nullity supplies the arithmetic projection corollary.
- Use finite rational probability mass functions for the integral-X window. Probabilities of events are finite sums; independence and conditioning can be proved by factoring these sums, avoiding general measure-theoretic probability at the finite layer.
- Fourier bias of `z` is `∑ v, μ(v) * (-1)^(dot(u,v))`, coerced to real. For a codimension-b subspace use annihilator cardinality `2^b` and orthogonality.

## 4. The hard analytic bridge

The existing export proves a location-of-zeros statement, not the new window inequality. Formalizing Lemma 2.1 requires a uniform explicit formula for primitive Dirichlet characters, a uniform count of zeros in intervals of ordinates, decay of the Mellin transform of the window, and the prime-power removal bound. One should first inspect existing Mathlib and vendored results on these ingredients; this roadmap does not assert all have ready-made formalized APIs. It is not legitimate to insert the window bound as a new global axiom and claim an unconditional formal proof of the downstream theorem. One can formally prove the finite combinatorial layer parametrized by the window bound while separately developing the analytic bridge.

## 5. Checks and trust boundary

Use `#print axioms` for the final downstream theorem, not just the imported adapter. Compile all modules with the pinned project, and check that no `sorryAx` or additional axioms occur. Compare the theorem statement to the mathematical one (including primitive characters, window support, distinctness and both distance quantifiers). Finite Python examples can supply test data but cannot discharge any unbounded theorem.
