import GRHArticle.SingularModuli.Moments
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Padics.Complex

/-!
# Convergence of normalized sparse-polynomial moments

This proves an explicit geometric envelope for the series in smd:lem:disk.
The field is Mathlib's p-adic complex field, which already carries its complete
ultrametric structure and the norm extending that of the p-adic rationals.
-/

namespace GRHArticle.SingularModuli

open Filter
open scoped BigOperators NNReal Topology

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The reciprocal of the lower bound for the p-adic exponential radius. -/
noncomputable def factorialGrowthBound (p : ℕ) : ℝ :=
  (p : ℝ) ^ (1 / ((p : ℝ) - 1))

theorem factorialGrowthBound_pos (p : ℕ) [Fact (Nat.Prime p)] :
    0 < factorialGrowthBound p :=
  Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _

theorem padicComplex_norm_natCast (m : ℕ) (hm : m ≠ 0) :
    ‖(m : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
  have hlift : ((m : ℚ_[p]) : PadicAlgCl p) = (m : PadicAlgCl p) := by
    exact map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) m
  rw [← PadicComplex.coe_natCast p m, ← hlift, PadicComplex.norm_extends' p,
    Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr hm), Padic.valuation_natCast]

/-- A geometric bound for the norms of the inverse factorials. -/
theorem norm_inv_factorial_le (k : ℕ) :
    ‖(k.factorial : ℂ_[p])⁻¹‖ ≤ factorialGrowthBound p ^ k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hnat : (p - 1) * padicValNat p k.factorial ≤ k := by
    by_cases h : k = 0
    · simp [h]
    · exact (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p h).le
  have hreal : ((p - 1 : ℕ) : ℝ) * (padicValNat p k.factorial : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hp.out.one_lt.le, Nat.cast_one, mul_comm] at hreal
  have hval : (padicValNat p k.factorial : ℝ) ≤ (k : ℝ) / ((p : ℝ) - 1) :=
    (le_div_iff₀ (sub_pos.mpr hp1)).mpr hreal
  rw [norm_inv, padicComplex_norm_natCast k.factorial (Nat.factorial_ne_zero _),
    zpow_neg, inv_inv, zpow_natCast, ← Real.rpow_natCast,
    factorialGrowthBound, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ p)]
  exact Real.rpow_le_rpow_of_exponent_le hp1.le
    (by simpa only [div_mul_eq_mul_div, one_mul] using hval)

theorem norm_moment_le_initial {K : Type*} [NormedField K] [IsUltrametricDist K]
    {t : ℕ} (n : Fin t → ℕ) (c : Fin t → K) (B : ℝ≥0)
    (hB : ∀ j < t, ‖moment n c j‖₊ ≤ B) (k : ℕ) : ‖moment n c k‖₊ ≤ B :=
  valuation_moment_le (NormedField.valuation (K := K)) n c B hB k

/-- One geometric estimate works for every point of the closed unit disk. -/
theorem norm_exponentialCoefficient_mul_pow_le {t : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a b y : ℂ_[p]) (B : ℝ≥0)
    (hB : ∀ j < t, ‖moment n (fun i => c i * a ^ n i) j‖₊ ≤ B)
    (hy : ‖y‖ ≤ 1) (k : ℕ) :
    ‖exponentialCoefficient n c a b k * y ^ k‖ ≤
      (B : ℝ) * (‖b‖ * factorialGrowthBound p) ^ k := by
  have hm : ‖moment n (fun i => c i * a ^ n i) k‖ ≤ (B : ℝ) :=
    NNReal.coe_le_coe.mpr (norm_moment_le_initial n _ B hB k)
  calc
    _ = ‖moment n (fun i => c i * a ^ n i) k‖ *
        (‖b‖ ^ k * ‖(k.factorial : ℂ_[p])⁻¹‖) * ‖y‖ ^ k := by
      simp only [exponentialCoefficient, div_eq_mul_inv, norm_mul, norm_pow]
    _ ≤ (B : ℝ) * (‖b‖ ^ k * factorialGrowthBound p ^ k) * (1 : ℝ) ^ k := by
      have hb₀ := pow_nonneg (norm_nonneg b) k
      have hF₀ := pow_nonneg (factorialGrowthBound_pos p).le k
      have hfactor := mul_le_mul_of_nonneg_left (norm_inv_factorial_le (p := p) k) hb₀
      have hproduct := mul_le_mul hm hfactor (mul_nonneg hb₀ (norm_nonneg _)) B.2
      exact mul_le_mul hproduct (pow_le_pow_left₀ (norm_nonneg y) hy k)
        (pow_nonneg (norm_nonneg y) k) (mul_nonneg B.2 (mul_nonneg hb₀ hF₀))
    _ = _ := by rw [one_pow, mul_one, mul_pow]

theorem summable_exponentialCoefficient_mul_pow {t : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a b y : ℂ_[p])
    (hb : ‖b‖ * factorialGrowthBound p < 1) (hy : ‖y‖ ≤ 1) :
    Summable (fun k => exponentialCoefficient n c a b k * y ^ k) := by
  let f : Fin t → ℝ≥0 := fun i => ‖moment n (fun j => c j * a ^ n j) i‖₊
  let B : ℝ≥0 := Finset.univ.sup f
  have hB : ∀ j < t, ‖moment n (fun i => c i * a ^ n i) j‖₊ ≤ B := by
    intro j hj
    change f ⟨j, hj⟩ ≤ Finset.univ.sup f
    exact Finset.le_sup (f := f) (Finset.mem_univ _)
  have hs := summable_geometric_of_lt_one (mul_nonneg (norm_nonneg b) (factorialGrowthBound_pos p).le) hb
  exact (hs.mul_left (B : ℝ)).of_norm_bounded
    (norm_exponentialCoefficient_mul_pow_le n c a b y B hB hy)

theorem tendsto_exponentialCoefficient_atTop_zero {t : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a b : ℂ_[p])
    (hb : ‖b‖ * factorialGrowthBound p < 1) :
    Tendsto (exponentialCoefficient n c a b) atTop (𝓝 0) := by
  have hs := summable_exponentialCoefficient_mul_pow n c a b 1 hb (by simp)
  simpa using hs.tendsto_atTop_zero

/-- A scaling element of depth r meets the strict geometric criterion
as soon as r > 1/(p-1). -/
theorem geometric_ratio_lt_one_of_depth (b : ℂ_[p]) (r : ℝ)
    (hdepth : 1 / ((p : ℝ) - 1) < r) (hb : ‖b‖ = (p : ℝ) ^ (-r)) :
    ‖b‖ * factorialGrowthBound p < 1 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [hb, factorialGrowthBound, ← Real.rpow_add (by positivity : (0 : ℝ) < p)]
  have h := Real.rpow_lt_rpow_of_exponent_lt h1
    (show -r + 1 / ((p : ℝ) - 1) < (0 : ℝ) by linarith)
  simpa only [Real.rpow_zero] using h

end GRHArticle.SingularModuli
