import IPRADerivations.Core.PolynomialImplications

/-!
# Completion of squares for two Gaussian exponents

Packet: `probability/normal_distribution_ipra_2026-11-16`:

* Lemma `lem:complete-square`, second identity:
  `(x − μ₀)²/(4σ₀²) + (x − μ₁)²/(4σ₁²) = A (x − m)² + C`, "where `A, m, C` are the rational expressions
  used in the Hellinger calculation";
* Proposition `prop:product-densities` for two densities with weights `w₀, w₁`: "The `x`-dependent part
  is `−½ ∑_j w_j (x − μ_j)²/σ_j²`. Completing the square gives `−(x − m)²/(2τ²)` plus a constant", with
  `τ^{−2} = ∑_j w_j/σ_j²`, `m = τ² ∑_j w_j μ_j/σ_j²`.

With `s_j = σ_j²` and cleared of denominators (closed sentences over the integers):

* `hellinger_square`:
  `(s₀ + s₁) (s₁ (x − μ₀)² + s₀ (x − μ₁)²) = ((s₀ + s₁) x − (μ₀ s₁ + μ₁ s₀))² + s₀ s₁ (μ₀ − μ₁)²`, i.e.
  `A = (s₀ + s₁)/(4 s₀ s₁)`, `m = (μ₀ s₁ + μ₁ s₀)/(s₀ + s₁)`, `C = (μ₀ − μ₁)²/(4 (s₀ + s₁))`;
* `product_square`: with `P = w₀ s₁ + w₁ s₀` (so `τ^{−2} = P/(s₀ s₁)`),
  `P (w₀ s₁ (x − μ₀)² + w₁ s₀ (x − μ₁)²) = (P x − (w₀ s₁ μ₀ + w₁ s₀ μ₁))² + w₀ w₁ s₀ s₁ (μ₀ − μ₁)²`,
  i.e. `m = (w₀ s₁ μ₀ + w₁ s₀ μ₁)/P`.

The first identity of `lem:complete-square` is in `Analysis/FiniteDifferenceIdentities`; for any number
of densities the identity is the weighted variance identity of `Probability/Variance`. The
normalization integrals are not formalized.
-/

namespace LeanProofs.IPRA.Probability.CompleteSquare

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

local notation "x" => (ZExp.var 0 : ZExp 7)
local notation "m₀" => (ZExp.var 1 : ZExp 7)
local notation "m₁" => (ZExp.var 2 : ZExp 7)
local notation "s₀" => (ZExp.var 3 : ZExp 7)
local notation "s₁" => (ZExp.var 4 : ZExp 7)
local notation "w₀" => (ZExp.var 5 : ZExp 7)
local notation "w₁" => (ZExp.var 6 : ZExp 7)

/-- `lem:complete-square`, second identity, cleared by `4 s₀ s₁ (s₀ + s₁)`. -/
theorem hellinger_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [] ((s₀ + s₁) * (s₁ * (x - m₀) ^ 2 + s₀ * (x - m₁) ^ 2),
        ((s₀ + s₁) * x - (m₀ * s₁ + m₁ * s₀)) ^ 2 + s₀ * s₁ * (m₀ - m₁) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `prop:product-densities` for two weighted densities, cleared of denominators. -/
theorem product_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 7)
      (imp [] ((w₀ * s₁ + w₁ * s₀) * (w₀ * s₁ * (x - m₀) ^ 2 + w₁ * s₀ * (x - m₁) ^ 2),
        ((w₀ * s₁ + w₁ * s₀) * x - (w₀ * s₁ * m₀ + w₁ * s₀ * m₁)) ^ 2 +
          w₀ * w₁ * s₀ * s₁ * (m₀ - m₁) ^ 2)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end LeanProofs.IPRA.Probability.CompleteSquare
