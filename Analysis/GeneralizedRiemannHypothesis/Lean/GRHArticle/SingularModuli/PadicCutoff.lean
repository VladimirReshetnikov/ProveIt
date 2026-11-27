import GRHArticle.SingularModuli.FactorialThreshold
import GRHArticle.SingularModuli.PadicConvergence
import GRHArticle.SingularModuli.Strassmann

/-!
# From factorial weights to the Strassmann cutoff

For the normalized exponential expansion of a sparse polynomial, the factorial
weight is the negative base-`p` exponent in the norm of its scaling factor.
Control of the initial moments therefore gives a coefficient norm cutoff for
Strassmann's theorem on the closed unit ball.
-/

namespace GRHArticle.SingularModuli

open scoped NNReal

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The norm of the exponential scaling factor at a specified depth. -/
theorem norm_exponentialFactor_eq_rpow_neg_factorialWeight {b : ℂ_[p]} {r : ℚ}
    (hb : ‖b‖ = (p : ℝ) ^ (-(r : ℝ))) (k : ℕ) :
    ‖b ^ k / (k.factorial : ℂ_[p])‖ = (p : ℝ) ^ (-(factorialWeight p r k : ℝ)) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [norm_div, norm_pow, hb, padicComplex_norm_natCast _ (Nat.factorial_ne_zero _),
    ← Real.rpow_mul_natCast hp₀.le, zpow_neg, div_inv_eq_mul, zpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_add hp₀]
  congr 1
  push_cast [factorialWeight]
  ring

/-- The coefficient norm is its moment norm times the explicit factorial factor. -/
theorem norm_exponentialCoefficient_eq_norm_moment_mul_rpow {t : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a : ℂ_[p]) {b : ℂ_[p]} {r : ℚ}
    (hb : ‖b‖ = (p : ℝ) ^ (-(r : ℝ))) (k : ℕ) :
    ‖exponentialCoefficient n c a b k‖ =
      ‖moment n (fun i ↦ c i * a ^ n i) k‖ * (p : ℝ) ^ (-(factorialWeight p r k : ℝ)) := by
  rw [exponentialCoefficient, norm_mul, norm_exponentialFactor_eq_rpow_neg_factorialWeight hb]

/-- One nonzero initial coefficient dominates every coefficient whose weight
is greater than all the initial weights. -/
theorem exists_initial_coefficient_dominating_factorialWeight {t : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a : ℂ_[p]) {b : ℂ_[p]} {r : ℚ}
    (hn : Function.Injective n) (hc : c ≠ 0) (ha : a ≠ 0)
    (hb : ‖b‖ = (p : ℝ) ^ (-(r : ℝ))) :
    ∃ i : Fin t, 0 < ‖exponentialCoefficient n c a b i‖ ∧ ∀ k : ℕ,
      (∀ j : Fin t, factorialWeight p r j < factorialWeight p r k) →
      ‖exponentialCoefficient n c a b k‖ < ‖exponentialCoefficient n c a b i‖ := by
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hb₀ : b ≠ 0 := norm_pos_iff.mp (by
    rw [hb]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans hp₁) _)
  obtain ⟨i, hi, hdom⟩ := exists_initial_coefficient_dominating_small_weights
    (NormedField.valuation (K := ℂ_[p])) n c a b hn hc ha hb₀
  refine ⟨i, norm_pos_iff.mpr hi, fun k hk ↦ ?_⟩
  exact NNReal.coe_lt_coe.mpr (hdom k (fun j ↦ by
    apply NNReal.coe_lt_coe.mp
    change ‖b ^ k / (k.factorial : ℂ_[p])‖ < ‖b ^ (j : ℕ) / ((j : ℕ).factorial : ℂ_[p])‖
    rw [norm_exponentialFactor_eq_rpow_neg_factorialWeight hb k,
      norm_exponentialFactor_eq_rpow_neg_factorialWeight hb (j : ℕ)]
    apply Real.rpow_lt_rpow_of_exponent_lt hp₁
    exact neg_lt_neg (by exact_mod_cast hk j)))

/-- The normalized exponential series has at most `N` distinct roots in the
unit ball when every weight after `N` is greater than each initial weight. -/
theorem encard_exponentialSeriesRoots_le_of_weight_cutoff {t N : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a : ℂ_[p]) {b : ℂ_[p]} {r : ℚ}
    (hn : Function.Injective n) (hc : c ≠ 0) (ha : a ≠ 0)
    (hr : 1 / ((p : ℝ) - 1) < (r : ℝ)) (hb : ‖b‖ = (p : ℝ) ^ (-(r : ℝ)))
    (hcut : ∀ k > N, ∀ j : Fin t, factorialWeight p r j < factorialWeight p r k) :
    {y : ℂ_[p] | ‖y‖ ≤ 1 ∧ seriesValue (exponentialCoefficient n c a b) y = 0}.encard ≤ N := by
  obtain ⟨i, hi, hdom⟩ := exists_initial_coefficient_dominating_factorialWeight n c a hn hc ha hb
  have hiN : (i : ℕ) ≤ N := by
    by_contra! h
    exact lt_irrefl _ (hcut i h i)
  exact encard_seriesRoots_le_of_cutoff
    (tendsto_exponentialCoefficient_atTop_zero n c a b (geometric_ratio_lt_one_of_depth b r hr hb))
    hiN hi (fun {k} hk ↦ hdom k (hcut k hk))

end GRHArticle.SingularModuli
