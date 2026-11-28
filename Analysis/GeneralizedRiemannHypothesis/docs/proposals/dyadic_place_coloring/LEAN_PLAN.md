# Lean integration plan (not compiled)

Baseline: ProveIt commit `89d12dd40424f1217fd818d84877b3da52396a3b`, readable `Analysis/GeneralizedRiemannHypothesis/Lean/grh` tree `2e133df63d7f4da6b3059c4195324f8e9187ba73`. Use its pinned Lean and Mathlib versions. No Lean installation was available in the artifact environment; the following is an implementation design, not verified Lean code.

## 1. Pure finite module

Suggested new module: `New/Reduction/Data/DyadicColor.lean`. The finite theorem should not import the number field or automorphic infrastructure. Use `Fin (2^s)` for exponents, `Fin K` for coordinates, and `Nat` for all components of the coloring. Avoid real logarithms in this module.

For positive `s,h`, `B ≥ 2`, define `M := 2^s`, `H := 2^h`, `K := (s+h-1)/h`. Define `r j e := (2^(j*h) * e.val) % M`, `cell j e := B * r j e / M`, `t j e := B * r j e % M`, `energy e := ∑ j, (t j e)^2`, and `radial e := (2*H^2*energy e)/(B*M^2)`.

Candidate interface (pseudocode, not an elaborated Lean declaration):

```text
weightedColorFree(s, B, h, hs, hB, hh):
  ∃ color : Fin (2^s) → Fin C,
    ∀ u v w : Fin (2^s), ∀ α β : ℕ,
      0 < α → 0 < β → α+β ≤ B →
      color u = color v → color v = color w →
      Nat.ModEq (2^s) ((α+β)*v.val) (α*u.val+β*w.val) →
      u = v ∧ v = w
  where C = B^K * (1 + (2*K*H^2)/B)
```

Alternatively target a product of `Fin B` coordinates and `Fin (1+(2*K*H^2)/B)`; its cardinality is exactly C. This is preferable to proving a mixed-radix encoding. Obtain a largest fiber in a finite set U by summing fiber cardinalities and comparing to the maximum. State the cardinality conclusion as `U.card ≤ S.card * C` to stay in naturals.

Proof obligations:

1. For distinct `u,w`, let `d := |u.val-w.val|`, and write `d = 2^v * a` with `a` odd and `v < s`. Put `j := (s-1-v)/h`. Prove `j < K`, `1 ≤ s-v-j*h ≤ h`. Thus the shifted difference is nonzero modulo M and its order divides H. In integer arithmetic the difference of the two residues is nonzero, and H times this difference is a multiple of M. Derive `M ≤ H * |r j u - r j w|` using integer absolute values.
2. For equal cell colors, the representatives differ by strictly less than M/B. For each j the weighted congruence is divisible by M, and its signed absolute value is strictly less than M. Hence it is zero. Use cross-multiplied integer inequalities instead of division where convenient.
3. In each coordinate lift the congruence to `n*t(v) = α*t(u)+β*t(w)`, where `n := α+β`. The squared-length identity in integers is
   `n*(α*E(u)+β*E(w)-n*E(v)) = α*β*∑ j,(t(j,u)-t(j,w))^2`.
   If the endpoints differ, separation and equal cell colors give `H^2*∑ diff^2 ≥ B^2*M^2`. Also `2*α*β ≥ n`, `n ≤ B`. Equality of radial bins gives the strict upper bound contradicting this inequality. One direct way to avoid denominators is to compare both sides after multiplication by `2*H^2`. Integer casts, `ring`, and positivity handle the identity; prove the finite-sum inequality independently of nonlinear automation.
4. If endpoints coincide, coordinate 0 and cell lifting imply equality of the midpoint too. No invertibility of n is required.
5. For h ≥ s, K=1 and the separation argument still applies; do not assume h ≤ s. Test α+β=B and repeated exponents. Test the empty subset separately if using maximum fibers.

## 2. Replace the existing sparse-set supplier

In `New/Reduction/Data/Existence.lean`, factor `Parameters.exists_large_isSparse` at the point where it obtains a weighted-free set of exponents. Preserve the remainder of the original proof (including the separate prime 2 case, signs, projection to the prime-to-p modulus, and order contradiction). Expose the generic transfer lemma taking S and `hfree`. The paper states this transfer in §4.

Add a wrapper producing `3 * l₀ s * 2^s ≤ T.card * W^4` for `1 ≤ W`, `2^s ≤ W^n`, `(2*l₀ s)^n ≤ W`, `2*l₀ s*(L+1)<2^s`, and positive n,s. Obtain h as the least integer with `W ≤ 2^h`; use `2^h < 2*W`. The old `exists_isSparse` can be kept as an adapter: drop unused premises and derive its original `W^6` bound by monotonicity. Then simplify `exists_isSparse_of_ranks`, removing its old separate counting argument. This first patch is intentionally small and does not change `Data`, `Parameters.IsSparse`, field weights, level primes, or the endpoint theorem.

## 3. Optional optimized interface

For any fixed `0 < η ≤ ε`, pick a dyadic block length h with `x^(η/8) ≤ 2^h < 2*x^(η/8)`. For `s ≤ 32*log x`, K is bounded by a constant depending only on η; `B=2*l₀ s = O(log x)`. Consequently `3*z*C = O((log x)^(K+1)*x^(η/4)) ≤ x^η` eventually. This version avoids formalizing a square-root optimization or a varying logarithmic exponent. The paper also gives a uniform explicit optimized bound using `ceil(sqrt(s*ceil(log₂ B)))`.

In `IsLargeScale.exists_isAdmissibleData`, receive T, class, cardinality and sparsity as a witness rather than constructing T inside the lemma via the window exponent n. Construct T after selecting m,r,s but **before** setting weights and choosing level primes, especially N. For the original ranks, `2^s ≥ x^11` and `2*z*(L+1) = O(x^10 log x)`, so the original cutoff premise holds. Pass the unchanged density premise by `x^η ≤ log b`. Retain the stronger density as an additional conclusion, not a change to `Data`.

Only after checking usages, remove the now-unneeded Behrend-specific `IsLargeScale.pow_le` and `mul_two_pow_le` fields. Keep prime-window exponent n, its Siegel–Walfisz prerequisites, and all unrelated scale conditions. Do not assume reducing the cardinality cost reduces the required `b`-scale: other lower bounds on b remain.

## 4. Endpoint and validation

The existing `Data.primeRemainder_le` can be generalized to retain the exact ratio of the two place counts, using the same identity and triangle inequality. Use the additional conclusion `ratio ≤ x^η`; no change to the analytic zero criterion is required. If other proposed main-inequality improvements are implemented, substitute their verified constants and exponents; otherwise retain the original fifth power of log b.

Acceptance checklist:

- Compile the finite module alone using the pinned toolchain.
- Compile the conservative transfer and adapter with unchanged public statements.
- Compile `Existence.lean`, then all consumers of `Data.sparse` (including near-pair and local-loss arguments), and the full `Lean/grh` library.
- Replay the endpoint using the original statement and axiom audit from the upstream verification. A successful finite regression or a compiled lemma does not verify the whole theorem.
- For the optimized patch, check that data choice still precedes weights and level selection; prove the additional ratio inequality at the exact source scales.
- Compare transitive imports, non-comment source lines and elaboration time with the original proof and with the already proposed replacements. Do not claim an actual code-size saving until measured.
