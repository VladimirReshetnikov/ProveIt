import FabiusFunction.ThueMorseGelfond
import FabiusFunction.ThueMorseNewmanQuantitative

/-!
# Sharpness of Gelfond's bound at every length

`ThueMorseGelfond` bounds the Thue–Morse exponential sum of *every*
length: `‖∑_{n<N} ε(n)·e^(inx)‖ ≤ (√3+1)·N^(log₄3)` uniformly in `x`
(`gelfond_general_bound_rpow`).  This module shows the exponent is
attained at every length, not only at the dyadic ones, by evaluating at
the Gelfond frequency `ω = e^(2πi/3)`: there the sum is the residue
decomposition

`∑_{n<N} ε(n)·ωⁿ = T₀(N) + ω·T₁(N) + ω²·T₂(N)`,

whose squared modulus is `T₀² + T₁² + T₂² - T₀T₁ - T₁T₂ - T₂T₀`.  With
`T₀ + T₁ + T₂ = E(N) ∈ {-1, 0, 1}` and Newman's `T₀(N) ≥ 1`, this is at
least `T₀(N)²`, so

`‖∑_{n<N} ε(n)·ωⁿ‖ ≥ N₃(N) ≥ N^(log₄3)/9`

by the quantitative Newman theorem.  Gelfond's exponent is therefore
sharp at every `N`, with the explicit two-sided bracket
`N^(log₄3)/9 ≤ sup_x ‖∑_{n<N} ε(n)·e^(inx)‖ ≤ (√3+1)·N^(log₄3)`.

* `gelfondRoot` — `ω = e^(2πi/3)`; `gelfondRoot_pow_three`,
  `one_add_gelfondRoot_add_sq`, `conj_gelfondRoot`.
* `sum_thueMorseSign_mul_pow_eq_residue` — the residue decomposition of
  `∑ ε(n)·ζⁿ` for **any** cube root of unity `ζ`.
* `norm_sq_add_gelfondRoot_mul` — `‖a + ωb + ω²c‖² = a²+b²+c²-ab-bc-ca`.
* `thueMorseResidueSum_three_zero_le_norm_sum` — **`N₃(N) ≤ ‖∑ ε(n)ωⁿ‖`**
  for every `N ≥ 1`.
* `gelfond_general_lower_bound`, `gelfond_general_two_sided` — the
  sharpness statement.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The Gelfond frequency on the unit circle: `ω = e^(2πi/3)`. -/
noncomputable def gelfondRoot : ℂ :=
  Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I)

theorem gelfondRoot_pow_three : gelfondRoot ^ 3 = 1 := by
  rw [gelfondRoot, ← Complex.exp_nat_mul, ← Complex.exp_two_pi_mul_I]
  congr 1
  push_cast
  ring

theorem norm_gelfondRoot : ‖gelfondRoot‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem gelfondRoot_ne_one : gelfondRoot ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  rw [gelfondRoot, Complex.exp_ofReal_mul_I_im, Complex.one_im] at him
  have hpos : 0 < Real.sin (2 * Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  linarith

/-- `1 + ω + ω² = 0`. -/
theorem one_add_gelfondRoot_add_sq :
    1 + gelfondRoot + gelfondRoot ^ 2 = 0 := by
  have hne : gelfondRoot - 1 ≠ 0 := sub_ne_zero.mpr gelfondRoot_ne_one
  have hprod : (gelfondRoot - 1) * (1 + gelfondRoot + gelfondRoot ^ 2) = 0 := by
    linear_combination gelfondRoot_pow_three
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd h hne
  · exact h

/-- `conj ω = ω²`. -/
theorem conj_gelfondRoot : (starRingEnd ℂ) gelfondRoot = gelfondRoot ^ 2 := by
  have h1 : gelfondRoot * (starRingEnd ℂ) gelfondRoot = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_gelfondRoot]
    norm_num
  have h2 : gelfondRoot * gelfondRoot ^ 2 = 1 := by
    rw [← pow_succ']
    exact gelfondRoot_pow_three
  have h0 : gelfondRoot ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
  exact mul_left_cancel₀ h0 (h1.trans h2.symm)

/-- **The residue decomposition**: for any `ζ` with `ζ³ = 1`,
`∑_{n<N} ε(n)·ζⁿ = T₀(N) + ζ·T₁(N) + ζ²·T₂(N)`. -/
theorem sum_thueMorseSign_mul_pow_eq_residue (ζ : ℂ) (h3 : ζ ^ 3 = 1)
    (N : ℕ) :
    ∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) * ζ ^ n =
      ((thueMorseResidueSum 3 0 N : ℝ) : ℂ) +
        ζ * ((thueMorseResidueSum 3 1 N : ℝ) : ℂ) +
        ζ ^ 2 * ((thueMorseResidueSum 3 2 N : ℝ) : ℂ) := by
  have hpow : ∀ n : ℕ, ζ ^ n = ζ ^ (n % 3) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow,
      one_mul]
  simp only [thueMorseResidueSum]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hpow n]
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;>
    simp [h] <;> ring

/-- `‖a + ωb + ω²c‖² = a² + b² + c² - ab - bc - ca` for real `a, b, c`. -/
theorem norm_sq_add_gelfondRoot_mul (a b c : ℝ) :
    ‖(a : ℂ) + gelfondRoot * b + gelfondRoot ^ 2 * c‖ ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
  have h := Complex.mul_conj ((a : ℂ) + gelfondRoot * b + gelfondRoot ^ 2 * c)
  rw [Complex.normSq_eq_norm_sq] at h
  have hc : (starRingEnd ℂ) ((a : ℂ) + gelfondRoot * b + gelfondRoot ^ 2 * c) =
      (a : ℂ) + gelfondRoot ^ 2 * b + gelfondRoot * c := by
    simp only [map_add, map_mul, map_pow, Complex.conj_ofReal, conj_gelfondRoot]
    linear_combination ((c : ℂ) * gelfondRoot) * gelfondRoot_pow_three
  have key : ((a : ℂ) + gelfondRoot * b + gelfondRoot ^ 2 * c) *
      ((a : ℂ) + gelfondRoot ^ 2 * b + gelfondRoot * c) =
      ((a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a : ℝ) : ℂ) := by
    push_cast
    linear_combination
      ((b : ℂ) ^ 2 + (c : ℂ) ^ 2 + (b : ℂ) * c * gelfondRoot) *
          gelfondRoot_pow_three +
        ((a : ℂ) * b + (a : ℂ) * c + (b : ℂ) * c) * one_add_gelfondRoot_add_sq
  rw [hc, key] at h
  exact_mod_cast h.symm

/-- **`N₃(N) ≤ ‖∑_{n<N} ε(n)·ωⁿ‖`** for every `N ≥ 1`: with
`a = T₀, b = T₁, c = T₂`, `a + b + c = E ∈ [-1,1]` and `a ≥ 1`,
`a²+b²+c²-ab-bc-ca - a² = ½(b-c)² + (b + (a-E)/2)² + ¼(a-E)(5a-E) ≥ 0`. -/
theorem thueMorseResidueSum_three_zero_le_norm_sum (N : ℕ) (hN : 1 ≤ N) :
    (thueMorseResidueSum 3 0 N : ℝ) ≤
      ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) * gelfondRoot ^ n‖ := by
  rw [sum_thueMorseSign_mul_pow_eq_residue gelfondRoot gelfondRoot_pow_three]
  set a : ℝ := (thueMorseResidueSum 3 0 N : ℝ) with ha_def
  set b : ℝ := (thueMorseResidueSum 3 1 N : ℝ) with hb_def
  set c : ℝ := (thueMorseResidueSum 3 2 N : ℝ) with hc_def
  have hsq := norm_sq_add_gelfondRoot_mul a b c
  have hsum : a + b + c = ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) := by
    rw [ha_def, hb_def, hc_def]
    exact_mod_cast thueMorseResidueSum_three_add N
  have hE := abs_le.mp (abs_sum_thueMorseSign_le_one N)
  have hE1 : (-1 : ℝ) ≤ ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) := by
    exact_mod_cast hE.1
  have hE2 : ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast hE.2
  have ha : (1 : ℝ) ≤ a := by
    rw [ha_def]
    exact_mod_cast newman_positivity N hN
  set E : ℝ := ((∑ n ∈ range N, thueMorseSign n : ℤ) : ℝ) with hE_def
  have hsq' : a ^ 2 ≤
      ‖(a : ℂ) + gelfondRoot * b + gelfondRoot ^ 2 * c‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (b - c), sq_nonneg (2 * b + a - E),
      mul_nonneg (show (0 : ℝ) ≤ a - E by linarith)
        (show (0 : ℝ) ≤ 5 * a - E by linarith)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq'

/-- **Gelfond's exponent is attained at every length**: at the Gelfond
frequency, `‖∑_{n<N} ε(n)·ωⁿ‖ ≥ N^(log₄3)/9` for every `N ≥ 1`. -/
theorem gelfond_general_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / 9 ≤
      ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) * gelfondRoot ^ n‖ :=
  (newman_lower_bound N hN).trans
    (thueMorseResidueSum_three_zero_le_norm_sum N hN)

/-- **The two-sided Gelfond bracket at every length**: for `N ≥ 1`,
`N^(log₄3)/9 ≤ ‖∑_{n<N} ε(n)·ωⁿ‖ ≤ (√3+1)·N^(log₄3)`; since the upper
bound holds uniformly in the frequency, the supremum over all real
frequencies lies in the same bracket. -/
theorem gelfond_general_two_sided (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (Real.logb 4 3) / 9 ≤
        ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) * gelfondRoot ^ n‖ ∧
      ‖∑ n ∈ range N, ((thueMorseSign n : ℤ) : ℂ) * gelfondRoot ^ n‖ ≤
        (Real.sqrt 3 + 1) * (N : ℝ) ^ (Real.logb 4 3) :=
  ⟨gelfond_general_lower_bound N hN,
    gelfond_general_bound_rpow (2 * Real.pi / 3) N⟩

end Fabius
