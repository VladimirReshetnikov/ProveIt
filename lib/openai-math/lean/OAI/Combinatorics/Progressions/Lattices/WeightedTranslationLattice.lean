import OAI.Combinatorics.Progressions.Geometry.WeightedTranslationIntegralCoordinates
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTranslationIntegralAction

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def weightedTranslationLattice (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) : Subgroup (weightedFiltration w d hwd).Group :=
  (integerWeightedLoweringSubgroup (shearWeight w d)).comap (weightedShearGroupHom w d hwd)

@[simp] theorem mem_weightedTranslationLattice (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).Group) :
    g ∈ weightedTranslationLattice w d hwd ↔
      polynomialShearExpAut (weightedShearEmbedding w d g.coord) ∈
        integerWeightedLoweringSubgroup (shearWeight w d) := Iff.rfl

theorem weightedTranslationLattice_eq_integral_preimage (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    weightedTranslationLattice w d hwd =
      PolynomialTranslationGroup.integralGroup.comap (bchTranslationHom w d hw hwd) :=
  (bchTranslation_integral_comap w d hw hwd).symm

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationLattice_inner_grid :
    scaledIntegerGrid d.factorial ⊆
      bchSubgroupCoordinates (weightedBasis w d hw) (weightedTranslationLattice w d hwd) := by
  intro x hx
  let X := (weightedBasis w d hw).equivFun.symm x
  have hX : (weightedBasis w d hw).equivFun X ∈ scaledIntegerGrid d.factorial := by
    simpa only [X,LinearEquiv.apply_symm_apply] using hx
  have hI := weightedBasis_scaledGrid_normalize w d hw d.factorial (Nat.factorial_pos d) X hX
  have he := polynomialShear_factorial_exp_integral d (shearWeight_le w d hwd)
    ((d.factorial : ℚ)⁻¹ • weightedShearEmbedding w d X) hI
  have hc : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  rw [smul_smul,mul_inv_cancel₀ hc,one_smul] at he
  exact he

theorem weightedTranslationLattice_outer_grid :
    bchSubgroupCoordinates (weightedBasis w d hw) (weightedTranslationLattice w d hwd) ⊆
      denominatorGrid d.factorial := by
  intro x hx
  let X := (weightedBasis w d hw).equivFun.symm x
  have hE : polynomialShearExpAut (weightedShearEmbedding w d X) ∈
      integerWeightedLoweringSubgroup (shearWeight w d) := hx
  have hI (i : σ ⊕ Unit) := polynomialShear_factorial_log_integral d (shearWeight_le w d hwd)
    (polynomialShearExpAut (weightedShearEmbedding w d X)) hE i
  simp only [polynomialShearLog_exp] at hI
  have h := (weightedBasis_denominatorGrid_iff w d hw d.factorial X).mpr hI
  simpa only [X,LinearEquiv.apply_symm_apply] using h

end Erdos3.PolynomialTranslationLie

end

end OAI
