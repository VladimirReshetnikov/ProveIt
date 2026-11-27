import GRHArticle.ProgressionFree.PolynomialIrreducibleDegrees
import GRHArticle.ProgressionFree.PolynomialRoughDensity
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An explicit lower bound on the rough density factor

Degree grouping bounds the prime-weight sum by the harmonic number. At the
article's binary cutoff this gives `c₂ > 2⁻¹²`.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Real
open scoped BigOperators Classical

variable (F : Type*) [Field F] [Fintype F]

theorem polynomialSmoothPrimes_weight_le_harmonic (L : ℕ) :
    ∑ p ∈ polynomialSmoothPrimes F L, (Fintype.card F : ℝ)⁻¹ ^ p.natDegree ≤ harmonic L := by
  let S := polynomialSmoothPrimes F L
  let q := (Fintype.card F : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hmaps (p : Polynomial F) (hp : p ∈ S) : p.natDegree ∈ Finset.Icc 1 L :=
    Finset.mem_Icc.mpr ⟨(mem_polynomialSmoothPrimes.mp hp).2.1.natDegree_pos,
      (mem_polynomialSmoothPrimes.mp hp).2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨hpos, hle⟩ := Finset.mem_Icc.mp hd
  have he : S.filter (fun p ↦ p.natDegree = d) =
      (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d) := by
    ext p
    simp only [S, Finset.mem_filter, mem_polynomialSmoothPrimes]
    constructor <;> rintro ⟨⟨hm, hi, _⟩, e⟩
    · exact ⟨⟨hm, hi, e.le⟩, e⟩
    · exact ⟨⟨hm, hi, e.le.trans hle⟩, e⟩
  have hdeg : (d : ℝ) * polynomialIrreducibleCount F d ≤ q ^ d := by
    dsimp [q]
    exact_mod_cast degree_mul_polynomialIrreducibleCount_le (F := F) d hpos
  calc
    ∑ p ∈ S.filter (fun p ↦ p.natDegree = d), q⁻¹ ^ p.natDegree =
        ∑ _p ∈ S.filter (fun p ↦ p.natDegree = d), q⁻¹ ^ d :=
      Finset.sum_congr rfl (fun _ hp ↦ by rw [(Finset.mem_filter.mp hp).2])
    _ = (polynomialIrreducibleCount F d : ℝ) / q ^ d := by
      simp [he, polynomialIrreducibleCount, inv_pow, div_eq_mul_inv]
    _ ≤ _ := by
      simp only [inv_eq_one_div]
      rw [div_le_div_iff₀ (pow_pos hq _) (by exact_mod_cast hpos : 0 < (d : ℝ))]
      simpa only [mul_comm, one_mul, mul_one] using hdeg

/-- A lower bound for the rough squarefree density, uniform in the finite field. -/
theorem polynomialRoughDensity_harmonic_lower (L : ℕ) :
    (1 - (Fintype.card F : ℝ)⁻¹) / exp (harmonic L) ≤ polynomialRoughDensity F L := by
  let w (p : Polynomial F) := (Fintype.card F : ℝ)⁻¹ ^ p.natDegree
  let S := polynomialSmoothPrimes F L
  have hw (p : Polynomial F) : 0 ≤ w p := by dsimp [w]; positivity
  have hprod : ∏ p ∈ S, (1 + w p) ≤ exp (harmonic L) :=
    (prod_one_add_le_exp_sum S hw).trans (exp_le_exp.mpr (polynomialSmoothPrimes_weight_le_harmonic F L))
  have hpos : 0 < ∏ p ∈ S, (1 + w p) := Finset.prod_pos fun p _ ↦ by linarith [hw p]
  have hq : 1 ≤ (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.one_lt_card (α := F)).le
  rw [polynomialRoughDensity, Finset.prod_inv_distrib, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos hprod)
    (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq))

theorem binary_polynomialRoughDensity_gt {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) : 1 / (2 : ℝ)^12 < polynomialRoughDensity F 480 := by
  have h := polynomialRoughDensity_harmonic_lower F 480
  rw [hF] at h
  have hExp : exp (harmonic 480) ≤ exp 1 * 480 := by
    simpa only [exp_add, Nat.cast_ofNat, exp_log (by norm_num : (0:ℝ)<480)] using
      exp_le_exp.mpr (harmonic_le_one_add_log 480)
  have h3 : exp 1 < 3 := exp_one_lt_d9.trans (by norm_num)
  apply lt_of_lt_of_le _ h
  rw [lt_div_iff₀ (exp_pos _)]
  change 1 / (2 : ℝ)^12 * exp (harmonic 480) < 1 - (2:ℝ)⁻¹
  linarith only [hExp, h3]

end GRHArticle.ProgressionFree
