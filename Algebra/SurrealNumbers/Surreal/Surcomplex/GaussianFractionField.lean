import Surreal.Foundations.OmnificSupportBounds
import Surreal.Surcomplex.MultiplierFormulas

/-!
# The actual surcomplex field is the Gaussian omnific fraction field

The identity asserted in `odg:def:sec:reconstruction` and following
`odg:frac:prop:gaussianfrac`. A single positive monomial simultaneously clears
both coordinates of every member of a lower-universe-small family.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Gaussian omnific elements are determined by their actual field values. -/
theorem gaussianOmnificToSurcomplex_injective :
    Function.Injective (gaussianOmnificToSurcomplex.{u}) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

/-- Purely infinite complex support is exactly purely infinite support in both real coordinates. -/
theorem isPurelyInfinite_iff_re_im (z : Surcomplex.{u}) :
    IsPurelyInfinite z ↔ SignSequence.IsPurelyInfinite z.re ∧
      SignSequence.IsPurelyInfinite z.im := by
  constructor
  · intro hz
    constructor
    · intro a ha
      have h := congrArg Complex.re (hz a ha)
      simpa only [coeff_rawNormalForm, Complex.zero_re] using h
    · intro a ha
      have h := congrArg Complex.im (hz a ha)
      simpa only [coeff_rawNormalForm, Complex.zero_im] using h
  · rintro ⟨hr, hi⟩ a ha
    rw [coeff_rawNormalForm]
    apply Complex.ext
    · exact hr a ha
    · exact hi a ha

/-- The actual purely infinite predicate agrees with the Gaussian constant-term kernel. -/
theorem isPurelyInfinite_gaussianOmnific_iff (z : GaussianOmnificInteger.{u}) :
    IsPurelyInfinite (gaussianOmnificToSurcomplex z) ↔
      z ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u}) :=
  (gaussianOmnific_inf_iff z).symm.trans (gaussianOmnific_purelyInfinite_iff_quadratic z).symm

/-- Purely infinite field elements have representatives in the Gaussian constant-term kernel. -/
theorem IsPurelyInfinite.exists_gaussianOmnific_kernel {z : Surcomplex.{u}} (hz : IsPurelyInfinite z) :
    ∃ w : GaussianOmnificInteger.{u}, w ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u}) ∧
      gaussianOmnificToSurcomplex w = z := by
  obtain ⟨w, hw⟩ := hz.exists_gaussianOmnific
  exact ⟨w, (isPurelyInfinite_gaussianOmnific_iff w).mp (hw.symm ▸ hz), hw⟩

/-- One positive actual real monomial clears an entire small surcomplex family. -/
theorem gaussianOmnific_monomial_clearing {ι : Type v} [Small.{u} ι]
    (s : ι → Surcomplex.{u}) :
    ∃ h : SignSequence.{u}, 0 < h ∧ ∀ i,
      ∃ z : GaussianOmnificInteger.{u}, z ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u}) ∧
        gaussianOmnificToSurcomplex z = ofReal (SignSequence.omegaPower h) * s i := by
  let coords : ι × Bool → SignSequence.{u} := fun p => if p.2 then (s p.1).im else (s p.1).re
  obtain ⟨h, hh, hs⟩ := SignSequence.omnific_monomial_clearing coords
  refine ⟨h, hh, fun i => ?_⟩
  apply IsPurelyInfinite.exists_gaussianOmnific_kernel
  rw [isPurelyInfinite_iff_re_im]
  have hc (b : Bool) : SignSequence.IsPurelyInfinite (SignSequence.omegaPower h * coords (i, b)) := by
    obtain ⟨w, hw, he⟩ := hs (i, b)
    rw [← he]
    exact (SignSequence.omnific_inf_iff w).mp
      ((SignSequence.omnific_purelyInfinite_iff_quadratic w).mp hw)
  constructor
  · simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, coords, Bool.false_eq_true,
      if_false] using hc false
  · simpa only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, coords, if_true] using hc true

/-- Every actual surcomplex is a quotient of two purely infinite Gaussian omnific integers. -/
theorem surcomplex_eq_gaussianOmnific_fraction (x : Surcomplex.{u}) :
    ∃ a b : GaussianOmnificInteger.{u}, a ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u}) ∧
      b ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u}) ∧ b ≠ 0 ∧
      x = gaussianOmnificToSurcomplex a / gaussianOmnificToSurcomplex b := by
  obtain ⟨h, hh, hs⟩ := gaussianOmnific_monomial_clearing (fun _ : PUnit => x)
  obtain ⟨a, ha, he⟩ := hs PUnit.unit
  obtain ⟨b, hb, hbv⟩ := (isPurelyInfinite_real_omegaPower h hh).exists_gaussianOmnific_kernel
  have hd : ofReal (SignSequence.omegaPower h) ≠ (0 : Surcomplex.{u}) :=
    (map_ne_zero_iff ofReal ofReal_injective).mpr (SignSequence.omegaPower_ne_zero h)
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · intro hz
    exact hd (hbv.symm.trans (by rw [hz, map_zero]))
  · rw [he, hbv, mul_div_cancel_left₀ _ hd]

/-- The actual surcomplex field is an algebra over the Gaussian omnific ring. -/
instance gaussianOmnificSurcomplexAlgebra : Algebra GaussianOmnificInteger.{u} Surcomplex.{u} :=
  gaussianOmnificToSurcomplex.toAlgebra

instance gaussianOmnificSurcomplexFaithfulSMul : FaithfulSMul GaussianOmnificInteger.{u} Surcomplex.{u} :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr gaussianOmnificToSurcomplex_injective

/-- The full actual field, rather than just its support subring, is the native fraction field. -/
instance gaussianOmnificSurcomplexIsFractionRing : IsFractionRing GaussianOmnificInteger.{u} Surcomplex.{u} := by
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _, _, _, h⟩ := surcomplex_eq_gaussianOmnific_fraction x
  exact ⟨a, b, h⟩

/-- The previously constructed embedding of the native Gaussian fraction field is onto. -/
theorem gaussianOmnificFractionEmbedding_surjective :
    Function.Surjective (gaussianOmnificFractionEmbedding.{u}) := by
  intro x
  obtain ⟨a, b, _, _, _, hx⟩ := surcomplex_eq_gaussianOmnific_fraction x
  refine ⟨algebraMap GaussianOmnificInteger.{u} (FractionRing GaussianOmnificInteger.{u}) a /
    algebraMap GaussianOmnificInteger.{u} (FractionRing GaussianOmnificInteger.{u}) b, ?_⟩
  have hi (c : GaussianOmnificInteger.{u}) : gaussianOmnificFractionEmbedding
      (algebraMap GaussianOmnificInteger.{u} (FractionRing GaussianOmnificInteger.{u}) c) =
      gaussianOmnificToSurcomplex c :=
    AugmentationFractionField.fractionEmbedding_algebraMap _ _ _ c
  rw [map_div₀, hi, hi]
  exact hx.symm

end
end Surreal.Surcomplex
