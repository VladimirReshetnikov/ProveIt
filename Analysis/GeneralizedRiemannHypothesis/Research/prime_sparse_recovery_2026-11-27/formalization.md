# Proposed Lean integration (not compiled)

No Lean executable was available in this session. This file is a mathematical dependency plan, not Lean code or a claim that any new statement is already formalized. Work in a separate Lake package with the vendored toolchain and Mathlib pin, not ProveIt's root Mathlib version.

## 1. Analytic boundary

Import the vendored `Main` module. The theorem `LFunction_eq_zero_re : DirichletLZerosOnLine` is the GRH input, along with `riemannHypothesis`. The half-plane theorem `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` rules out right-boundary zeros. The reported audit commands are in `scripts/PrintAxioms.lean`. Do not add these as custom axioms if the source package can be imported.

Mathematical interfaces to formalize:

1. Fix a nonnegative smooth compactly supported function W on [1,2] with integral 1. Prove a uniform local zero-count estimate with multiplicity for primitive Dirichlet L-functions; prove the Mellin inversion/contour formula and square-root error using critical-line zeros.
2. Replace von Mangoldt by prime-only weights using Chebyshev's bound. Induced characters differ at primes dividing the modulus; bound the sum of their log primes by log modulus.
3. Define the finite character dictionary using a dependent sum over positive q ≤ Q and primitive `DirichletCharacter ℂ q`. Include q=1. Show that inflation of two primitive characters to lcm(q,r) gives identical characters iff they have the same conductor and agree. This is the crucial off-diagonal nonprincipal lemma. Prime divisors of either modulus must map to zero.
4. Prove weighted Gram entrywise deviation O(log(2Q)/sqrt(x)), then the finite Bernoulli sampling lemma. The explicit finite probability space is all subsets of the prime interval, with product weights. A real Bernstein inequality with variance bound M, applied to real and imaginary components, and the union bound imply existence of a subset with m between M/2 and 3M/2. No independence between pairs of columns is needed.

## 2. Independent finite-dimensional core

Use finite row and column types `I, J`, and a matrix `A : I → J → ℂ` with each entry norm ≤ 1. Let `m = Fintype.card I > 0` and assume the entrywise Gram deviation `‖m⁻¹ * ∑ i, conj (A i j) * A i l - if j=l then 1 else 0‖ ≤ μ` (in the implementation insert the appropriate parentheses and real-to-complex casts). Define ℓ¹ by finite sums and ℓ∞ by finite maximum; avoid relying on any particular existing matrix norm instance. Define `Ah i = ∑ j, A i j * h j`.

For E a row finset, U its complement, S a column finset of cardinality ≤ k, the independent algebraic lemma is:

```
∑ j∈S, ‖h j‖ ≤ (k/m) * ∑ i∈U, ‖Ah i‖ + k*(μ + |E|/m)*∑ j, ‖h j‖.
```

Proof: expand the Gram error and use the triangle inequality, the entry bound, and finite sum interchange. Bound each coordinate of h and sum over S. Formally, it is easier to avoid the maximum norm entirely by proving the coordinate bound separately for each j.

For any c,h and S, split sums over S and its complement to prove

```
‖c+h‖₁ - ‖c‖₁ ≥ ‖h‖₁ - 2‖h|S‖₁ - 2‖c|Sᶜ‖₁.
```

For error vector b supported on T ⊆ U and ordinary noise w, derive

```
‖b+w-Ah‖₁,U - ‖b+w‖₁,U ≥ ‖Ah‖₁,U - 2|T|‖h‖₁ - 2‖w‖₁,U.
```

Set the decoder objective J(z) = ‖z‖₁ + (2k/m)‖y-Az‖₁,U. The first formal theorem can avoid a compactness proof by quantifying over any `z` with `J z ≤ J c`. Set h=z-c, add the inequalities, cancel the finite residual sum, and use `linarith` or explicit ordered-field inequalities. If margin d=1-2kμ-2k(|E|+2t)/m>0, then

```
d * ‖z-c‖₁ ≤ 2‖c|Sᶜ‖₁ + (4k/m)‖w‖₁,U.
```

The sparsity case chooses S containing the support, and finite sums of norms vanish iff every coordinate vanishes. Existence of a minimizer is a separate classical compactness result: continuous objective, sublevel set bounded because J(z) ≥ ‖z‖₁, and closed in a finite-dimensional real normed space.

## 3. Sharpness and arithmetic transfer

At a prime modulus q ≡ 1 mod 4k, the multiplicative group of the finite field is cyclic. Let θ generate its character group and ω=θ^((q−1)/(2k)); use subgroup order to prove θω^j is nonprincipal and primitive for 0≤j<2k. The sum of a geometric progression vanishes except at the selected phase. On sampled primes dividing q, all terms are zero. Pigeonhole gives a phase class of cardinality ≤ floor(m/(2k)). Split its support into two sets of k character coefficients, then partition the differing rows after erasure into two error supports of cardinality ≤t. Construct the same observation vector for the two different coefficient vectors. This argument is fully finite and does not require the imported theorem. The existence of q in the stated conductor range uses the analytic bound separately.

Finally, the Euler-product/logarithmic-derivative expansion at Re(s)>1 identifies normalized prime coefficients with the mixture. No additional zero theorem is required.

## 4. Audit criteria

- Keep the analytic and finite-dimensional components separate; the latter should have no dependency on `Main`.
- Check `#print axioms` for each exported new result. No `sorry`, `admit`, custom axioms, or unverified `native_decide` should occur in the proof.
- The Python certificate verifies a specific finite Gram bound, not the uniform theorem. It could be separately formalized with exact rational arithmetic and a proof of the trigonometric approximation bound.
