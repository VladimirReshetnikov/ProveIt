import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

 theorem allocatedBlock_card_le_tuples (a : LayerSamplerAxis I n) :
    Fintype.card (B a) ≤ Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) := by
  apply Fintype.card_le_of_injective
    (fun b : B a => (⟨a, b, ⟨0, Nat.zero_lt_succ _⟩⟩ : PrincipalTupleIndex B (layerSamplerDegree I n)))
  intro b c hbc
  simpa using hbc

 theorem allocatedAffine_block_dimensions {D : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α O D) :
    ∀ a, (Fintype.card (B a) : ℝ) ≤ D :=
  fun a => (Nat.cast_le.mpr (allocatedBlock_card_le_tuples B a)).trans hd.tuples

 theorem allocatedAffine_parameter_dimensions {D : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α O D) :
    (Fintype.card (PolynomialParameter
      ((G × Option α) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
      (JointBlockParameter B (layerSamplerDegree I n) α)) : ℝ) ≤
        D * (D + 1) + D * D + D + 1 := by
  have hslots : (∑ a : LayerSamplerAxis I n,
      (Fintype.card (SamplerCoefficientSlot G B (layerSamplerDegree I n) a) : ℝ)) ≤ D * D := by
    apply affineLog_sum_le _ hd.axes hd.nonneg
    intro a
    exact hd.coefficients a.1
  have hG := hd.kernel_variables
  have hα := hd.cube
  have hparam := hd.parameters
  have hD := hd.nonneg
  simp only [PolynomialParameter, Fintype.card_option, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_one]
  simp only [JointBlockParameter, BlockParameter, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_option, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hparam
  gcongr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

omit [DecidableEq α] [∀ j, Nonempty (O j)] in
 theorem allocatedAffine_log_costs_le_envelope [DecidableEq α] [∀ j, Nonempty (O j)]
    (A T : ℝ≥0) {D E F : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α O D) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    allocatedAffineRadiusLog (O := O) (α := α) B A T E F ≤
      2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2 ∧
    allocatedAffineToleranceLog (G := G) (O := O) (α := α) B A T E F ≤
      affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F := by
  have hB := allocatedAffine_block_dimensions B hd
  have hh (a : LayerSamplerAxis I n) : (layerSamplerDegree I n a : ℝ) ≤ D :=
    hd.layer_degree B a.1
  have hO (a : LayerSamplerAxis I n) : (Fintype.card (O a.1) : ℝ) ≤ D := hd.rows a.1
  constructor
  · apply (Finset.sup'_le_iff _ _).mpr
    intro partition _
    exact add_le_add (mul_le_mul_of_nonneg_left
      (partitionedAffineInputLog_le_envelope (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
        (α := α) (layerSamplerDegree I n) partition A T hd.nonneg hd.axes hd.cube hB hO hh hE hF)
      (by norm_num)) le_rfl
  · apply (Finset.sup'_le_iff _ _).mpr
    intro partition _
    exact partitionedAffineToleranceLog_le_envelope (G := G) (Z := G × Option α)
      (B := B) (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
      (layerSamplerDegree I n) partition A T m hd.nonneg hd.axes hd.cube hB hO hh hE hF
      (allocatedAffine_parameter_dimensions B hd)

end Erdos3.VectorPolynomial

end

end OAI
