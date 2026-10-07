import OAI.Combinatorics.Progressions.Linear.RealFirstCoefficientBasis

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ)

def firstCoefficientIndexEmbedding : FirstCoefficientIndex w ω ↪ AdaptedBasisIndex w ω where
  toFun z := ⟨z.val, (Nat.le_add_right _ 1).trans z.property.le⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : AdaptedBasisIndex w ω => z.val) h

variable [Fintype σ] [Fintype ι] (s : ℕ) (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

@[instance_reducible] noncomputable def firstCoefficientIndexFintype :
    Fintype (FirstCoefficientIndex w ω) := by
  letI := adaptedBasisIndexFintype w ω s hw hω
  exact Fintype.ofInjective (firstCoefficientIndexEmbedding w ω) (firstCoefficientIndexEmbedding w ω).injective

include hw hω in
theorem firstCoefficientIndex_card_le [Fintype (FirstCoefficientIndex w ω)] :
    Fintype.card (FirstCoefficientIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  let := adaptedBasisIndexFintype w ω s hw hω
  exact (Fintype.card_le_of_injective _ (firstCoefficientIndexEmbedding w ω).injective).trans
    (adaptedBasisIndex_card_le w ω s hw hω)

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hw hF

theorem firstCoefficientModule_finiteDimensional : FiniteDimensional ℚ (F.FirstCoefficientModule w) := by
  let := firstCoefficientIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  exact (F.firstCoefficientBasis b ω hF w).finiteDimensional_of_finite

theorem realFirstCoefficientModule_finiteDimensional :
    FiniteDimensional ℝ (F.RealFirstCoefficientModule w) := by
  let := firstCoefficientIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  exact (F.realFirstCoefficientBasis b ω hF w).finiteDimensional_of_finite

theorem realFirstCoefficientModule_finrank_le :
    finrank ℝ (F.RealFirstCoefficientModule w) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  let := firstCoefficientIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hF)
  rw [finrank_eq_card_basis (F.realFirstCoefficientBasis b ω hF w)]
  exact firstCoefficientIndex_card_le w ω s hw (F.adaptedBasis_weight_le_step b ω hF)

end Erdos3.NilpotentLieFiltration

end

end OAI
