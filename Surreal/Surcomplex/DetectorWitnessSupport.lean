import Surreal.Surcomplex.SupportRingHahnEmbedding
import Surreal.Surcomplex.IntersectiveDetector
import Surreal.HahnSeries.DetectorWitnessSupport

/-!
# Controlled detector witnesses on the actual omnific carriers

The actual surreal and surcomplex conclusions of `odg:def:prop:support`.
Witnesses are constructed by finite polynomial evaluation inside the
actual support rings. Canonical normal-form embeddings prove the support
bounds at actual Conway growth exponents and the actual degree identities.
-/

universe u
namespace Surreal

open Foundations IntersectivePolynomial
open scoped Pointwise

noncomputable section

private theorem polynomial_control_map {Γ K H : Type*} [AddCommGroup Γ]
    [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K] [CommRing H] [Algebra K H]
    (φ : H →+* HahnSeries.nonpositiveSupportSubring Γ K)
    (hc : ∀ c : K, φ (algebraMap K H c) = HahnSeries.nonpositiveConstants c)
    (r α : K) (hr : r ^ 2 = 13) (hα : α ≠ 0) (a : H) :
    HahnSeries.DetectorWitnessControl (φ a)
      (φ ((witnessSPolynomial r α).eval₂ (algebraMap K H) a))
      (φ ((witnessTPolynomial r α).eval₂ (algebraMap K H) a)) := by
  have hcomp : φ.comp (algebraMap K H) = HahnSeries.nonpositiveConstants := RingHom.ext hc
  rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, hcomp]
  exact HahnSeries.explicit_detectorWitnessControl r α hr hα (φ a)

namespace Foundations.SignSequence

attribute [local instance] nonnegativeSupportRealAlgebra

/-- The explicit affine witness, constructed in the actual real support ring. -/
def detectorWitnessT (r α : ℝ) (a : nonnegativeSupportSubring.{u}) : nonnegativeSupportSubring.{u} :=
  (witnessTPolynomial r α).eval₂ realConstants a

/-- The explicit degree-five witness, constructed in the actual real support ring. -/
def detectorWitnessS (r α : ℝ) (a : nonnegativeSupportSubring.{u}) : nonnegativeSupportSubring.{u} :=
  (witnessSPolynomial r α).eval₂ realConstants a

/-- The source bounds stated on actual Conway supports and leading growth exponents. -/
structure DetectorWitnessControl (a s t : nonnegativeSupportSubring.{u}) : Prop where
  equation : a * s = value t
  support_t : SmallNormalForm.support (SmallNormalForm.normalForm t.val) ⊆
    SmallNormalForm.support (SmallNormalForm.normalForm a.val) ∪ {0}
  support_s : SmallNormalForm.support (SmallNormalForm.normalForm s.val) ⊆
    ⋃ j ≤ 5, j • (SmallNormalForm.support (SmallNormalForm.normalForm a.val) ∪ {0})
  degrees : a ≠ realConstants (constantCoeff a) →
    leadingExponent t.val = leadingExponent a.val ∧ leadingExponent s.val = 5 • leadingExponent a.val

/-- At nonconstant input, neither witness vanishes, so the leading exponents are actual degrees. -/
theorem DetectorWitnessControl.nonzero {a s t : nonnegativeSupportSubring.{u}}
    (h : DetectorWitnessControl a s t) (ha : a ≠ realConstants (constantCoeff a)) :
    a.val ≠ 0 ∧ s.val ≠ 0 ∧ t.val ≠ 0 := by
  have hp := nonnegativeSupport_leadingExponent_pos a ha
  have hd := h.degrees ha
  have hs : 0 < leadingExponent s.val := by
    rw [hd.2]
    exact nsmul_pos hp (by decide : 5 ≠ 0)
  have ht : 0 < leadingExponent t.val := hd.1 ▸ hp
  exact ⟨fun hz => by simp [hz] at hp,
    fun hz => by simp [hz] at hs, fun hz => by simp [hz] at ht⟩

/-- The actual polynomial witnesses satisfy the source equation and both geometric bounds. -/
theorem explicit_detectorWitnessControl (r α : ℝ) (hr : r ^ 2 = 13) (hα : α ≠ 0)
    (a : nonnegativeSupportSubring.{u}) :
    DetectorWitnessControl a (detectorWitnessS r α a) (detectorWitnessT r α a) := by
  have h := polynomial_control_map supportHahnEmbedding supportHahnEmbedding_constant r α hr hα a
  change HahnSeries.DetectorWitnessControl (supportHahnEmbedding a)
    (supportHahnEmbedding (detectorWitnessS r α a))
    (supportHahnEmbedding (detectorWitnessT r α a)) at h
  refine ⟨witnessPolynomials_identity r α hr a, ?_, ?_, ?_⟩
  · have ht := Set.image_mono (f := growthExponentEquiv.symm) h.support_t
    change growthExponentEquiv.symm '' (rawNormalForm (detectorWitnessT r α a).val).support ⊆
      growthExponentEquiv.symm '' ((rawNormalForm a.val).support ∪ {0}) at ht
    simpa only [Set.image_union, Set.image_singleton, map_zero, growthSupport_image] using ht
  · have hs := Set.image_mono (f := growthExponentEquiv.symm) h.support_s
    change growthExponentEquiv.symm '' (rawNormalForm (detectorWitnessS r α a).val).support ⊆
      growthExponentEquiv.symm '' (⋃ j ≤ 5, j • ((rawNormalForm a.val).support ∪ {0})) at hs
    simpa only [growthSumsets_image, growthSupport_image] using hs
  · intro ha
    have hd := h.degrees (supportHahnEmbedding_nonconstant a ha)
    constructor
    · simpa only [one_nsmul] using leadingExponent_eq_of_hahnDegree
        (detectorWitnessT r α a) a 1 (by simpa only [one_nsmul] using hd.1)
    · exact leadingExponent_eq_of_hahnDegree (detectorWitnessS r α a) a 5 hd.2

/-- Every actual omnific integer with nonzero constant term has controlled actual witnesses. -/
theorem omnific_detector_certificate_control (a : OmnificInteger.{u})
    (ha : omnificConstantCoeff a ≠ 0) :
    ∃ s t : OmnificInteger.{u}, DetectorWitnessControl a.val s.val t.val := by
  let ct : nonnegativeSupportSubring.{u} →ₐ[ℝ] ℝ :=
    { __ := constantCoeff
      commutes' := constantCoeff_realConstants }
  let c : ℤ := omnificConstantCoeff a
  have hc : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hca : ct a.val = (c : ℝ) :=
    (CoefficientPullback.embedding_retraction constantCoeff (Int.castRingHom ℝ)
      Int.cast_injective a).symm
  obtain ⟨b, d, hbd⟩ := integer_modular_value c ha
  let r : ℝ := Real.sqrt 13
  have hr : r ^ 2 = 13 := by norm_num [r, Real.sq_sqrt]
  let α : ℝ := ((b : ℝ) - r) / (c : ℝ)
  have hα : α ≠ 0 := witness_slope_ne_zero (Int.castRingHom ℝ) Int.cast_injective
    integer_value_ne_zero r hr b c hc
  have hm := witnessPolynomials_augmentation ct (Int.castRingHom ℝ) r hr b c d hc hbd a.val hca
  change constantCoeff (detectorWitnessT r α a.val) = (b : ℝ) ∧
    constantCoeff (detectorWitnessS r α a.val) = (d : ℝ) ∧ _ at hm
  exact ⟨⟨detectorWitnessS r α a.val, ⟨d, hm.2.1.symm⟩⟩,
    ⟨detectorWitnessT r α a.val, ⟨b, hm.1.symm⟩⟩,
    explicit_detectorWitnessControl r α hr hα a.val⟩

end Foundations.SignSequence

namespace Surcomplex

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The affine witness constructed in the actual complex support ring. -/
def detectorWitnessT (r α : ℂ) (a : nonnegativeSupportSubring.{u}) : nonnegativeSupportSubring.{u} :=
  (witnessTPolynomial r α).eval₂ complexConstants a

/-- The degree-five witness constructed in the actual complex support ring. -/
def detectorWitnessS (r α : ℂ) (a : nonnegativeSupportSubring.{u}) : nonnegativeSupportSubring.{u} :=
  (witnessSPolynomial r α).eval₂ complexConstants a

/-- The literal support and degree claims on the actual complex normal forms. -/
structure DetectorWitnessControl (a s t : nonnegativeSupportSubring.{u}) : Prop where
  equation : a * s = value t
  support_t : growthSupport t.val ⊆ growthSupport a.val ∪ {0}
  support_s : growthSupport s.val ⊆ ⋃ j ≤ 5, j • (growthSupport a.val ∪ {0})
  degrees : a ≠ complexConstants (constantCoeff a) →
    leadingExponent t.val = leadingExponent a.val ∧ leadingExponent s.val = 5 • leadingExponent a.val

/-- The actual complex witnesses cannot vanish when the input is nonconstant. -/
theorem DetectorWitnessControl.nonzero {a s t : nonnegativeSupportSubring.{u}}
    (h : DetectorWitnessControl a s t) (ha : a ≠ complexConstants (constantCoeff a)) :
    a.val ≠ 0 ∧ s.val ≠ 0 ∧ t.val ≠ 0 := by
  have hp := nonnegativeSupport_leadingExponent_pos a ha
  have hd := h.degrees ha
  have hs : 0 < leadingExponent s.val := by
    rw [hd.2]
    exact nsmul_pos hp (by decide : 5 ≠ 0)
  have ht : 0 < leadingExponent t.val := hd.1 ▸ hp
  exact ⟨fun hz => by simp [hz] at hp,
    fun hz => by simp [hz] at hs, fun hz => by simp [hz] at ht⟩

/-- The same identities use the native degree with minus infinity at zero. -/
theorem DetectorWitnessControl.growthDegrees {a s t : nonnegativeSupportSubring.{u}}
    (h : DetectorWitnessControl a s t) (ha : a ≠ complexConstants (constantCoeff a)) :
    growthDegree t.val = growthDegree a.val ∧ growthDegree s.val = 5 • growthDegree a.val := by
  obtain ⟨ha0, hs0, ht0⟩ := h.nonzero ha
  obtain ⟨ht, hs⟩ := h.degrees ha
  rw [growthDegree_of_ne_zero ha0, growthDegree_of_ne_zero hs0, growthDegree_of_ne_zero ht0]
  exact ⟨congrArg (fun x : SignSequence.{u} => (x : WithBot SignSequence.{u})) ht,
    by simpa only [WithBot.coe_nsmul] using
      congrArg (fun x : SignSequence.{u} => (x : WithBot SignSequence.{u})) hs⟩

/-- Actual surcomplex polynomial witnesses retain the Hahn support and degree control. -/
theorem explicit_detectorWitnessControl (r α : ℂ) (hr : r ^ 2 = 13) (hα : α ≠ 0)
    (a : nonnegativeSupportSubring.{u}) :
    DetectorWitnessControl a (detectorWitnessS r α a) (detectorWitnessT r α a) := by
  have h := polynomial_control_map supportHahnEmbedding supportHahnEmbedding_constant r α hr hα a
  change HahnSeries.DetectorWitnessControl (supportHahnEmbedding a)
    (supportHahnEmbedding (detectorWitnessS r α a))
    (supportHahnEmbedding (detectorWitnessT r α a)) at h
  refine ⟨witnessPolynomials_identity r α hr a, ?_, ?_, ?_⟩
  · have ht := Set.image_mono (f := SignSequence.growthExponentEquiv.symm) h.support_t
    change SignSequence.growthExponentEquiv.symm '' (rawNormalForm (detectorWitnessT r α a).val).support ⊆
      SignSequence.growthExponentEquiv.symm '' ((rawNormalForm a.val).support ∪ {0}) at ht
    simpa only [Set.image_union, Set.image_singleton, map_zero, growthSupport_image] using ht
  · have hs := Set.image_mono (f := SignSequence.growthExponentEquiv.symm) h.support_s
    change SignSequence.growthExponentEquiv.symm '' (rawNormalForm (detectorWitnessS r α a).val).support ⊆
      SignSequence.growthExponentEquiv.symm '' (⋃ j ≤ 5, j • ((rawNormalForm a.val).support ∪ {0})) at hs
    simpa only [SignSequence.growthSumsets_image, growthSupport_image] using hs
  · intro ha
    have hd := h.degrees (supportHahnEmbedding_nonconstant a ha)
    constructor
    · simpa only [one_nsmul] using leadingExponent_eq_of_hahnDegree
        (detectorWitnessT r α a) a 1 (by simpa only [one_nsmul] using hd.1)
    · exact leadingExponent_eq_of_hahnDegree (detectorWitnessS r α a) a 5 hd.2

/-- Every actual Gaussian omnific integer with nonzero constant term has controlled witnesses. -/
theorem gaussianOmnific_detector_certificate_control (a : GaussianOmnificInteger.{u})
    (ha : gaussianOmnificConstantCoeff a ≠ 0) :
    ∃ s t : GaussianOmnificInteger.{u}, DetectorWitnessControl a.val s.val t.val := by
  let c : GaussianInt := gaussianOmnificConstantCoeff a
  have hc : GaussianInt.toComplex c ≠ 0 :=
    (map_ne_zero_iff GaussianInt.toComplex GaussianInt.toComplex_injective).mpr ha
  have hca : constantCoeffAlgHom a.val = GaussianInt.toComplex c :=
    (CoefficientPullback.embedding_retraction constantCoeff GaussianInt.toComplex
      GaussianInt.toComplex_injective a).symm
  obtain ⟨b, d, hbd⟩ := gaussian_modular_value c ha
  let r : ℂ := (Real.sqrt 13 : ℂ)
  have hr : r ^ 2 = 13 := by
    dsimp [r]
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  let α : ℂ := (GaussianInt.toComplex b - r) / GaussianInt.toComplex c
  have hα : α ≠ 0 := witness_slope_ne_zero GaussianInt.toComplex GaussianInt.toComplex_injective
    gaussian_value_ne_zero r hr b c hc
  have hm := witnessPolynomials_augmentation constantCoeffAlgHom GaussianInt.toComplex
    r hr b c d hc hbd a.val hca
  change constantCoeff (detectorWitnessT r α a.val) = GaussianInt.toComplex b ∧
    constantCoeff (detectorWitnessS r α a.val) = GaussianInt.toComplex d ∧ _ at hm
  exact ⟨⟨detectorWitnessS r α a.val, ⟨d, hm.2.1.symm⟩⟩,
    ⟨detectorWitnessT r α a.val, ⟨b, hm.1.symm⟩⟩,
    explicit_detectorWitnessControl r α hr hα a.val⟩

end Surcomplex
end
end Surreal
