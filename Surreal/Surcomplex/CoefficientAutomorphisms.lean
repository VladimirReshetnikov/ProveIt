import Surreal.Surcomplex.SmallHahnRealization
import Surreal.Surcomplex.GaussianOmnificAutomorphisms
import Surreal.HahnSeries.CoefficientMapping

/-!
# Coefficientwise automorphisms of the actual surcomplex field

The field-lift construction of `odg:def:prop:coeffaut`. No continuity,
real-axis preservation or analytic regularity is required of the complex
automorphism. Every input retains exactly its original small support.
-/

universe u v
namespace Surreal.Surcomplex
noncomputable section

private theorem small_coefficient_image (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u}) :
    Small.{u} (HahnSeries.coefficientEquiv σ (rawNormalForm z)).support := by
  rw [HahnSeries.support_coefficientEquiv]
  infer_instance

private def coefficientMap (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u}) : Surcomplex.{u} :=
  ofSmallHahn (HahnSeries.coefficientEquiv σ (rawNormalForm z)) (small_coefficient_image σ z)

private theorem rawNormalForm_coefficientMap (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u}) :
    rawNormalForm (coefficientMap σ z) = HahnSeries.coefficientEquiv σ (rawNormalForm z) :=
  rawNormalForm_ofSmallHahn _ _

private theorem coefficientMap_inverse (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u}) :
    coefficientMap σ.symm (coefficientMap σ z) = z := by
  apply rawNormalForm_injective
  rw [rawNormalForm_coefficientMap, rawNormalForm_coefficientMap]
  apply _root_.HahnSeries.ext
  funext a
  exact σ.symm_apply_apply ((rawNormalForm z).coeff a)

/-- Apply any ordinary complex automorphism to every canonical complex coefficient. -/
def coefficientAutomorphism (σ : ℂ ≃+* ℂ) : Surcomplex.{u} ≃+* Surcomplex.{u} where
  toFun := coefficientMap σ
  invFun := coefficientMap σ.symm
  left_inv := coefficientMap_inverse σ
  right_inv := coefficientMap_inverse σ.symm
  map_add' z w := by
    apply rawNormalForm_injective
    rw [rawNormalForm_coefficientMap, rawNormalForm_add, map_add, rawNormalForm_add,
      rawNormalForm_coefficientMap, rawNormalForm_coefficientMap]
  map_mul' z w := by
    apply rawNormalForm_injective
    rw [rawNormalForm_coefficientMap, rawNormalForm_mul, map_mul, rawNormalForm_mul,
      rawNormalForm_coefficientMap, rawNormalForm_coefficientMap]

@[simp] theorem rawNormalForm_coefficientAutomorphism (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u}) :
    rawNormalForm (coefficientAutomorphism σ z) = HahnSeries.coefficientEquiv σ (rawNormalForm z) :=
  rawNormalForm_coefficientMap σ z

/-- The literal coefficientwise formula from the source. -/
@[simp] theorem coeff_coefficientAutomorphism (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u})
    (a : _root_.Surreal.{u}ᵒᵈ) :
    (rawNormalForm (coefficientAutomorphism σ z)).coeff a = σ ((rawNormalForm z).coeff a) := by
  rw [rawNormalForm_coefficientAutomorphism, HahnSeries.coeff_coefficientEquiv]

/-- Every exponent remains supported exactly when it was supported before. -/
theorem support_coefficientAutomorphism (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u}) :
    (rawNormalForm (coefficientAutomorphism σ z)).support = (rawNormalForm z).support := by
  rw [rawNormalForm_coefficientAutomorphism, HahnSeries.support_coefficientEquiv]

@[simp] theorem coefficientAutomorphism_inverse (σ : ℂ ≃+* ℂ) (z : Surcomplex.{u}) :
    coefficientAutomorphism σ.symm (coefficientAutomorphism σ z) = z :=
  coefficientMap_inverse σ z

/-- On ordinary constants the lift is exactly the chosen complex automorphism. -/
@[simp] theorem coefficientAutomorphism_ofComplex (σ : ℂ ≃+* ℂ) (c : ℂ) :
    coefficientAutomorphism σ (ofComplex c : Surcomplex.{u}) = ofComplex (σ c) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_coefficientAutomorphism, rawNormalForm_ofComplex, rawNormalForm_ofComplex]
  exact _root_.HahnSeries.map_single σ.toRingHom.toZeroHom

/-- All real Conway monomials are fixed because their nonzero coefficient is one. -/
theorem coefficientAutomorphism_real_omegaPower (σ : ℂ ≃+* ℂ) (a : Foundations.SignSequence.{u}) :
    coefficientAutomorphism σ (ofReal (Foundations.SignSequence.omegaPower a)) =
      ofReal (Foundations.SignSequence.omegaPower a) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_coefficientAutomorphism, rawNormalForm_real_omegaPower]
  change HahnSeries.mapCoefficients σ.toRingHom (_root_.HahnSeries.single _ 1) = _
  rw [HahnSeries.mapCoefficients_single, map_one]

/-- Coefficient lifting preserves identity and composition as a native group homomorphism. -/
def coefficientAutomorphismHom : (ℂ ≃+* ℂ) →* (Surcomplex.{u} ≃+* Surcomplex.{u}) where
  toFun := coefficientAutomorphism
  map_one' := by
    apply RingEquiv.ext
    intro z
    apply rawNormalForm_injective
    apply _root_.HahnSeries.ext
    funext a
    exact coeff_coefficientAutomorphism 1 z a
  map_mul' σ ρ := by
    apply RingEquiv.ext
    intro z
    apply rawNormalForm_injective
    apply _root_.HahnSeries.ext
    funext a
    change (rawNormalForm (coefficientAutomorphism (σ * ρ) z)).coeff a =
      (rawNormalForm (coefficientAutomorphism σ (coefficientAutomorphism ρ z))).coeff a
    rw [coeff_coefficientAutomorphism, coeff_coefficientAutomorphism, coeff_coefficientAutomorphism]
    rfl

/-- The lift preserves the actual nonnegative-growth support ring. -/
theorem coefficientAutomorphism_mem_supportRing (σ : ℂ ≃+* ℂ) {z : Surcomplex.{u}}
    (hz : z ∈ nonnegativeSupportSubring) : coefficientAutomorphism σ z ∈ nonnegativeSupportSubring := by
  rw [mem_supportRing_iff_rawNormalForm] at hz ⊢
  intro a ha
  rw [coeff_coefficientAutomorphism, hz a ha, map_zero]

/-- Strong summability is preserved without any continuity assumption on the coefficients. -/
theorem StronglySummable.coefficientAutomorphism {ι : Type v} {f : ι → Surcomplex.{u}}
    (hf : StronglySummable f) (σ : ℂ ≃+* ℂ) :
    StronglySummable (fun i => Surcomplex.coefficientAutomorphism σ (f i)) := by
  apply stronglySummable_of_hahnFamily (HahnSeries.mapCoefficientsFamily σ.toRingHom hf.toHahnFamily)
  intro i
  exact (rawNormalForm_coefficientAutomorphism σ (f i)).symm

/-- Coefficient lifting commutes with every existing actual strong sum. -/
theorem coefficientAutomorphism_strongSum {ι : Type v} [Small.{u} ι]
    {f : ι → Surcomplex.{u}} (hf : StronglySummable f) (σ : ℂ ≃+* ℂ) :
    coefficientAutomorphism σ (strongSum f hf) =
      strongSum (fun i => coefficientAutomorphism σ (f i)) (hf.coefficientAutomorphism σ) := by
  apply rawNormalForm_injective
  rw [rawNormalForm_coefficientAutomorphism, rawNormalForm_strongSum, rawNormalForm_strongSum]
  have hs : (hf.coefficientAutomorphism σ).toHahnFamily =
      HahnSeries.mapCoefficientsFamily σ.toRingHom hf.toHahnFamily := by
    ext1 i
    exact rawNormalForm_coefficientAutomorphism σ (f i)
  rw [hs]
  exact HahnSeries.mapCoefficients_hsum σ.toRingHom hf.toHahnFamily

end
end Surreal.Surcomplex
