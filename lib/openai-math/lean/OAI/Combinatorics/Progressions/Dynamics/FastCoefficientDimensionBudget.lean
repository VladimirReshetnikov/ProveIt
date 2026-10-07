import OAI.Combinatorics.Progressions.Estimates.FirstCoefficientDimension
import OAI.Combinatorics.Progressions.Estimates.ReducedSymbolDimensions

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

def fastCoefficientMatrixParameter (s : ℕ) (p : ℝ) : ℝ :=
  reducedMatrixParameter s p + (p + (s + 3)) ^ (s + 3) * (p + 1) + p + 2

theorem fastCoefficientMatrixParameter_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ fastCoefficientMatrixParameter s p := by
  have hr := reducedMatrixParameter_nonneg s hp
  unfold fastCoefficientMatrixParameter
  positivity

theorem le_fastCoefficientMatrixParameter (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fastCoefficientMatrixParameter s p := by
  have hr := reducedMatrixParameter_nonneg s hp
  have hd : 0 ≤ (p + (s + 3)) ^ (s + 3) * (p + 1) := by positivity
  unfold fastCoefficientMatrixParameter
  linarith

theorem fastCoefficient_matrix_dimensions
    {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    [Fintype (FirstCoefficientIndex w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p) :
    (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ fastCoefficientMatrixParameter s p ∧
    ((Fintype.card (FirstCoefficientIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤
      fastCoefficientMatrixParameter s p := by
  have hr := (F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ).2.1
  rw [Fintype.card_sum, Nat.cast_add] at hr
  have hr0 := reducedMatrixParameter_nonneg s hp
  have hd0 : 0 ≤ (p + (s + 3)) ^ (s + 3) := by positivity
  have hfac0 : 0 ≤ (p + (s + 3)) ^ (s + 3) * (p + 1) := by positivity
  have hrq : reducedMatrixParameter s p ≤ fastCoefficientMatrixParameter s p := by
    unfold fastCoefficientMatrixParameter
    linarith
  have hdf : (Fintype.card (FirstCoefficientIndex w ω) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
    have h := (Nat.cast_le (α := ℝ).mpr
      (firstCoefficientIndex_card_le w ω (s + 1) hw (F.adaptedBasis_weight_le_step e ω hF))).trans
      (symbol_dimension_bound_le_power (s + 1) (Fintype.card ι) (Fintype.card σ) hp hι hσ)
    simpa [Nat.cast_add, Nat.add_assoc, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using h
  have hdq : (p + (s + 3)) ^ (s + 3) * (p + 1) ≤ fastCoefficientMatrixParameter s p := by
    unfold fastCoefficientMatrixParameter
    linarith
  refine ⟨((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hr).trans hrq,
    ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hr).trans hrq, ?_, ?_⟩
  · exact hdf.trans ((by nlinarith : (p + (s + 3)) ^ (s + 3) ≤
      (p + (s + 3)) ^ (s + 3) * (p + 1)).trans hdq)
  · rw [Nat.cast_mul]
    exact (mul_le_mul hdf (hκ.trans (by linarith)) (Nat.cast_nonneg _) hd0).trans hdq

end Erdos3.NilpotentLieFiltration

end

end OAI
