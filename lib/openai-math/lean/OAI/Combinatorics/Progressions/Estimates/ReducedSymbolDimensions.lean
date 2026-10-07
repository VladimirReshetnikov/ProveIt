import OAI.Combinatorics.Progressions.Linear.SquareBasisGeometry

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hF hw in
theorem quotientTopSymbolIndex_finite : Finite (QuotientTopSymbolIndex s w ω) :=
  symbolBasisIndex_finite w (fun i : QuotientTopBasisIndex s ω => ω i.val) s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF))

include hF hw in
theorem reducedSquareSymbolIndex_finite : Finite (ReducedSquareSymbolIndex s w ω) :=
  symbolBasisIndex_finite w (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val) s hw
    (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))

include hF hw in
theorem quotientTopSymbolIndex_card_le [Fintype (QuotientTopSymbolIndex s w ω)] :
    Fintype.card (QuotientTopSymbolIndex s w ω) ≤
      Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have h := symbolBasisIndex_card_le w (fun i : QuotientTopBasisIndex s ω => ω i.val) s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF)
      (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF))
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)))

include hF hw in
theorem reducedSquareSymbolIndex_card_le [Fintype (ReducedSquareSymbolIndex s w ω)] :
    Fintype.card (ReducedSquareSymbolIndex s w ω) ≤
      2 * (Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s) := by
  have h := symbolBasisIndex_card_le w
    (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val) s hw
    (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
  have hc : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
    (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
  exact h.trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right ((Fintype.card σ + 1) ^ s)
      (Nat.mul_le_mul_right (s + 1) hc))

def reducedMatrixParameter (s : ℕ) (p : ℝ) : ℝ :=
  3 * (p + (s + 2)) ^ (s + 2) * (p + 1) + 2 * p + 2

theorem reducedMatrixParameter_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedMatrixParameter s p := by
  unfold reducedMatrixParameter
  positivity

theorem le_reducedMatrixParameter (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ reducedMatrixParameter s p := by
  have h : 0 ≤ 3 * (p + (s + 2)) ^ (s + 2) * (p + 1) := by positivity
  unfold reducedMatrixParameter
  linarith

include hF hw in
theorem reduced_lift_matrix_dimensions {κ : Type*} [Fintype κ]
    [Fintype (ReducedSquareSymbolIndex s w ω)] [Fintype (QuotientTopSymbolIndex s w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p) :
    2 * (Fintype.card ι : ℝ) ≤ reducedMatrixParameter s p ∧
      (Fintype.card (ReducedSquareSymbolIndex s w ω ⊕ QuotientTopSymbolIndex s w ω) : ℝ) ≤
        reducedMatrixParameter s p ∧
      ((Fintype.card (ReducedSquareSymbolIndex s w ω) * Fintype.card κ : ℕ) : ℝ) ≤
        reducedMatrixParameter s p := by
  let d := (p + (s + 2)) ^ (s + 2)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hB : (Fintype.card (QuotientTopSymbolIndex s w ω) : ℝ) ≤ d :=
    (Nat.cast_le.mpr (F.quotientTopSymbolIndex_card_le e ω hF w hw)).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hS : (Fintype.card (ReducedSquareSymbolIndex s w ω) : ℝ) ≤ 2 * d := by
    have hh := Nat.cast_le (α := ℝ).mpr (F.reducedSquareSymbolIndex_card_le e ω hF w hw)
    rw [Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ) (by norm_num))
  have hlarge : 3 * d * (p + 1) ≤ reducedMatrixParameter s p := by
    dsimp only [reducedMatrixParameter, d]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ 3 * d * (p + 1) := by positivity
    dsimp only [reducedMatrixParameter]
    change 2 * (Fintype.card ι : ℝ) ≤ 3 * d * (p + 1) + 2 * p + 2
    linarith
  · rw [Fintype.card_sum, Nat.cast_add]
    calc
      _ ≤ 3 * d := by linarith
      _ ≤ 3 * d * (p + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ p + 1 by linarith)
          (show 0 ≤ 3 * d by positivity)
      _ ≤ _ := hlarge
  · rw [Nat.cast_mul]
    calc
      _ ≤ (2 * d) * p := mul_le_mul hS hκ (Nat.cast_nonneg _) (by positivity)
      _ ≤ (3 * d) * (p + 1) :=
        mul_le_mul (by linarith) (by linarith) hp (by positivity)
      _ ≤ _ := hlarge

end Erdos3.NilpotentLieFiltration

end

end OAI
