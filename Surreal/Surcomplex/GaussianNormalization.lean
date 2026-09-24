import Surreal.Surcomplex.GaussianNormalizationDensity

/-!
# The actual Gaussian omnific normalization

The properness, density, zero-conductor and non-generation clauses of
`osq:nm:thm:complexnormal`. Its actual-field support and constant slices
are proved in `GaussianIntegralSlices`. The fixed model is separate.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Every nonzero Gaussian omnific element has an integral-unit multiple outside the original ring. -/
theorem gaussianOmnific_normalization_unit_obstruction (a : GaussianOmnificInteger.{u}) (ha : a ≠ 0) :
    ∃ v : integralClosure GaussianOmnificInteger Surcomplex.{u}, IsUnit v ∧
      0 < modulus (gaussianOmnificToSurcomplex a * v) ∧
      modulus (gaussianOmnificToSurcomplex a * v) < 1 ∧
      ¬ ∃ b : GaussianOmnificInteger, gaussianOmnificToSurcomplex b = gaussianOmnificToSurcomplex a * v := by
  have ha' : gaussianOmnificToSurcomplex a ≠ 0 := by
    intro h
    apply ha
    apply gaussianOmnificToSurcomplex_injective
    simpa only [map_zero] using h
  have hm : 0 < modulus (gaussianOmnificToSurcomplex a) := modulus_pos ha'
  obtain ⟨u, hu, hu0, huε⟩ := SignSequence.omnific_exists_small_integral_unit
    (1 / modulus (gaussianOmnificToSurcomplex a)) (by positivity)
  let v := realNormalizationToGaussian u
  have he : modulus (gaussianOmnificToSurcomplex a * (v : Surcomplex)) =
      modulus (gaussianOmnificToSurcomplex a) * (u : SignSequence) := by
    rw [modulus_mul, show (v : Surcomplex) = ofReal (u : SignSequence) from rfl,
      modulus_ofReal, abs_of_pos hu0]
  have hp : 0 < modulus (gaussianOmnificToSurcomplex a * (v : Surcomplex)) := by
    rw [he]
    exact mul_pos hm hu0
  have hl : modulus (gaussianOmnificToSurcomplex a * (v : Surcomplex)) < 1 := by
    rw [he]
    have h := (lt_div_iff₀ hm).mp huε
    nlinarith
  refine ⟨v, hu.map realNormalizationToGaussian, hp, hl, ?_⟩
  rintro ⟨b, hb⟩
  have hb0 : b ≠ 0 := by
    intro hzero
    rw [← hb, hzero, map_zero, modulus_zero] at hp
    exact (lt_irrefl 0) hp
  have h := one_le_gaussianOmnific_modulus b hb0
  rw [hb] at h
  exact (not_lt_of_ge h) hl

/-- The conductor from Gaussian omnific integers to their actual normalization is zero. -/
theorem gaussianOmnific_normalization_conductor_eq_bot :
    NormalizationConductor.conductor GaussianOmnificInteger Surcomplex.{u} = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  by_contra hn
  obtain ⟨v, _, _, _, hv⟩ := gaussianOmnific_normalization_unit_obstruction a hn
  exact hv (ha v)

/-- No lower-universe-small set generates the actual Gaussian normalization. -/
theorem gaussianOmnific_normalization_not_small_generated (s : Set Surcomplex.{u}) [Small.{u} s] :
    Algebra.adjoin GaussianOmnificInteger s ≠ integralClosure GaussianOmnificInteger Surcomplex := by
  intro he
  obtain ⟨d, hd, _, hs⟩ := gaussianOmnific_adjoin_conductor_nonzero s
  have hmem : d ∈ NormalizationConductor.conductor GaussianOmnificInteger Surcomplex.{u} := by
    intro x
    obtain ⟨z, _, hz⟩ := hs (x : Surcomplex) (he.symm ▸ x.property)
    exact ⟨z, hz⟩
  rw [gaussianOmnific_normalization_conductor_eq_bot, Ideal.mem_bot] at hmem
  exact hd hmem

/-- The normalization properly contains the original Gaussian omnific algebra. -/
theorem gaussianOmnific_bot_lt_integralClosure :
    (⊥ : Subalgebra GaussianOmnificInteger Surcomplex.{u}) <
      integralClosure GaussianOmnificInteger Surcomplex := by
  apply bot_lt_iff_ne_bot.mpr
  intro h
  exact gaussianOmnific_normalization_not_small_generated (∅ : Set Surcomplex.{u})
    (by simpa only [Algebra.adjoin_empty] using h.symm)

/-- The actual-field Gaussian normalization theorem, with both support and constant slices. -/
theorem gaussianOmnific_normalization :
    (⊥ : Subalgebra GaussianOmnificInteger Surcomplex.{u}) < integralClosure GaussianOmnificInteger Surcomplex ∧
      integralClosure GaussianOmnificInteger Surcomplex.{u} < ⊤ ∧
      Dense (integralClosure GaussianOmnificInteger Surcomplex.{u} : Set Surcomplex) ∧
      NormalizationConductor.conductor GaussianOmnificInteger Surcomplex.{u} = ⊥ ∧
      (∀ (s : Set Surcomplex.{u}) [Small.{u} s],
        Algebra.adjoin GaussianOmnificInteger s ≠ integralClosure GaussianOmnificInteger Surcomplex) ∧
      (integralClosure GaussianOmnificInteger Surcomplex.{u}).toSubring.comap
        nonnegativeSupportSubring.subtype = (integralClosure ℤ ℂ).toSubring.comap constantCoeff ∧
      (integralClosure GaussianOmnificInteger Surcomplex.{u}).toSubring.comap ofComplex =
        (integralClosure ℤ ℂ).toSubring :=
  ⟨gaussianOmnific_bot_lt_integralClosure, gaussianOmnific_integralClosure_lt_top,
    gaussianOmnific_integralClosure_dense, gaussianOmnific_normalization_conductor_eq_bot,
    gaussianOmnific_normalization_not_small_generated, gaussianOmnific_integralClosure_support_slice,
    gaussianOmnific_integralClosure_complex_slice⟩

end
end Surreal.Surcomplex
