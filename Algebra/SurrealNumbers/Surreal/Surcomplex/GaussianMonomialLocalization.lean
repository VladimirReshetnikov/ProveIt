import Surreal.Foundations.OmnificMonomialLocalization

/-!
# Gaussian localization at a positive real monomial

The actual Gaussian instance of `osq:prop:locsupport`. The native
localization embeds in the actual surcomplex field, and membership is
exactly a natural-multiple lower bound on its full complex growth support.
Both real coordinates lie in the corresponding real localization.
The resulting nonzero domain is neither a field nor birthday-universe-small;
it has no nonzero small ring target or small unital module.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The native Gaussian localization at a real monomial maps into the actual complex field. -/
def gaussianOmnificMonomialLocalizationEmbedding (a : SignSequence.{u}) (ha : 0 < a) :
    Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha)) →+* Surcomplex.{u} :=
  IsLocalization.Away.lift (omnificToGaussian (SignSequence.omnificMonomial a ha))
    (g := gaussianOmnificToSurcomplex) (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff ofReal ofReal_injective).mpr (SignSequence.omegaPower_ne_zero a)))

@[simp] theorem gaussianOmnificMonomialLocalizationEmbedding_algebraMap
    (a : SignSequence.{u}) (ha : 0 < a) (f : GaussianOmnificInteger.{u}) :
    gaussianOmnificMonomialLocalizationEmbedding a ha
      (algebraMap _ (Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha))) f) =
        gaussianOmnificToSurcomplex f := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The Gaussian monomial localization embeds in the actual complex field. -/
theorem gaussianOmnificMonomialLocalizationEmbedding_injective (a : SignSequence.{u}) (ha : 0 < a) :
    Function.Injective (gaussianOmnificMonomialLocalizationEmbedding a ha) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (omnificToGaussian (SignSequence.omnificMonomial a ha))) _).mpr
  intro x y
  simp only [gaussianOmnificMonomialLocalizationEmbedding_algebraMap]
  constructor
  · intro h
    simpa only [gaussianOmnificMonomialLocalizationEmbedding_algebraMap] using
      congrArg (gaussianOmnificMonomialLocalizationEmbedding a ha) h
  · intro h
    exact congrArg _ (gaussianOmnificToSurcomplex_injective h)

/-- Gaussian fractions have a natural power of the chosen real monomial as denominator. -/
theorem mem_gaussianOmnificMonomialLocalization_range_iff (a : SignSequence.{u}) (ha : 0 < a)
    (x : Surcomplex.{u}) :
    x ∈ (gaussianOmnificMonomialLocalizationEmbedding a ha).range ↔
      ∃ (n : ℕ) (f : GaussianOmnificInteger.{u}),
        x * ofReal (SignSequence.omegaPower (n * a)) = gaussianOmnificToSurcomplex f := by
  let m := omnificToGaussian (SignSequence.omnificMonomial a ha)
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨n, f, h⟩ := IsLocalization.Away.surj m z
    refine ⟨n, f, ?_⟩
    have he := congrArg (gaussianOmnificMonomialLocalizationEmbedding a ha) h
    simpa only [map_mul, map_pow, gaussianOmnificMonomialLocalizationEmbedding_algebraMap,
      m, gaussianOmnificToSurcomplex_of_omnific, SignSequence.omnificToSurreal_monomial,
      SignSequence.omegaPower_nat_mul] using he
  · rintro ⟨n, f, h⟩
    let z := IsLocalization.mk' (Localization.Away m) f
      (⟨m ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers m)
    refine ⟨z, ?_⟩
    apply mul_right_cancel₀ ((map_ne_zero_iff ofReal ofReal_injective).mpr
      (SignSequence.omegaPower_ne_zero (n * a)))
    rw [h, SignSequence.omegaPower_nat_mul, map_pow]
    have he := congrArg (gaussianOmnificMonomialLocalizationEmbedding a ha)
      (IsLocalization.mk'_spec (Localization.Away m) f
        (⟨m ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers m))
    simpa only [map_mul, map_pow, gaussianOmnificMonomialLocalizationEmbedding_algebraMap,
      m, gaussianOmnificToSurcomplex_of_omnific, SignSequence.omnificToSurreal_monomial] using he

/-- Real elements of the real localization belong to the Gaussian localization. -/
theorem ofReal_mem_gaussianOmnificMonomialLocalization (a : SignSequence.{u}) (ha : 0 < a)
    {x : SignSequence.{u}} (hx : x ∈ (SignSequence.omnificMonomialLocalizationEmbedding a ha).range) :
    ofReal x ∈ (gaussianOmnificMonomialLocalizationEmbedding a ha).range := by
  obtain ⟨n, f, hf⟩ := (SignSequence.mem_omnificMonomialLocalization_range_iff a ha x).mp hx
  apply (mem_gaussianOmnificMonomialLocalization_range_iff a ha _).mpr
  refine ⟨n, omnificToGaussian f, ?_⟩
  rw [← map_mul, hf, gaussianOmnificToSurcomplex_of_omnific]

/-- Membership is equivalent to membership of both real coordinates in the real localization. -/
theorem mem_gaussianOmnificMonomialLocalization_iff_coordinates (a : SignSequence.{u}) (ha : 0 < a)
    (x : Surcomplex.{u}) :
    x ∈ (gaussianOmnificMonomialLocalizationEmbedding a ha).range ↔
      x.re ∈ (SignSequence.omnificMonomialLocalizationEmbedding a ha).range ∧
      x.im ∈ (SignSequence.omnificMonomialLocalizationEmbedding a ha).range := by
  constructor
  · intro hx
    obtain ⟨n, f, hf⟩ := (mem_gaussianOmnificMonomialLocalization_range_iff a ha x).mp hx
    constructor
    · apply (SignSequence.mem_omnificMonomialLocalization_range_iff a ha _).mpr
      refine ⟨n, gaussianOmnificRe f, ?_⟩
      have h := congrArg (fun z : Surcomplex.{u} => z.re) hf
      simpa only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
        gaussianOmnificRe_value] using h
    · apply (SignSequence.mem_omnificMonomialLocalization_range_iff a ha _).mpr
      refine ⟨n, gaussianOmnificIm f, ?_⟩
      have h := congrArg (fun z : Surcomplex.{u} => z.im) hf
      simpa only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add,
        gaussianOmnificIm_value] using h
  · rintro ⟨hr, hi⟩
    have hI : I ∈ (gaussianOmnificMonomialLocalizationEmbedding a ha).range := by
      refine ⟨algebraMap _ _ gaussianOmnificI, ?_⟩
      rw [gaussianOmnificMonomialLocalizationEmbedding_algebraMap, gaussianOmnificI_value]
    rw [← re_add_im_mul_I x]
    exact Subring.add_mem _ (ofReal_mem_gaussianOmnificMonomialLocalization a ha hr)
      (Subring.mul_mem _ (ofReal_mem_gaussianOmnificMonomialLocalization a ha hi) hI)

/-- The Gaussian monomial localization contains every ordinary complex coefficient. -/
theorem ofComplex_mem_gaussianOmnificMonomialLocalization
    (a : SignSequence.{u}) (ha : 0 < a) (z : ℂ) :
    ofComplex z ∈ (gaussianOmnificMonomialLocalizationEmbedding a ha).range := by
  rw [mem_gaussianOmnificMonomialLocalization_iff_coordinates]
  exact ⟨SignSequence.ofReal_mem_omnificMonomialLocalization a ha z.re,
    SignSequence.ofReal_mem_omnificMonomialLocalization a ha z.im⟩

/-- Complex support consists exactly of the union of the real coordinate supports. -/
theorem growthCoeff_ne_zero_iff_coordinates (x : Surcomplex.{u}) (b : SignSequence.{u}) :
    growthCoeff x b ≠ 0 ↔
      b ∈ SmallNormalForm.support (SmallNormalForm.normalForm x.re) ∨
      b ∈ SmallNormalForm.support (SmallNormalForm.normalForm x.im) := by
  rw [growthCoeff, coeff_rawNormalForm]
  change (⟨_, _⟩ : ℂ) ≠ 0 ↔ _ ≠ 0 ∨ _ ≠ 0
  simp only [ne_eq, Complex.ext_iff, Complex.zero_re, Complex.zero_im, not_and_or]
  rfl

/-- Gaussian localization membership is precisely a lower bound on full complex growth support. -/
theorem mem_gaussianOmnificMonomialLocalization_iff_support (a : SignSequence.{u}) (ha : 0 < a)
    (x : Surcomplex.{u}) :
    x ∈ (gaussianOmnificMonomialLocalizationEmbedding a ha).range ↔
      ∃ n : ℕ, ∀ b, growthCoeff x b ≠ 0 → -(n * a) ≤ b := by
  rw [mem_gaussianOmnificMonomialLocalization_iff_coordinates,
    SignSequence.mem_omnificMonomialLocalization_iff_support,
    SignSequence.mem_omnificMonomialLocalization_iff_support]
  constructor
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    refine ⟨n + m, fun b hb => ?_⟩
    rcases (growthCoeff_ne_zero_iff_coordinates x b).mp hb with hr | hi
    · have h := hn b hr
      have hma := mul_nonneg (Nat.cast_nonneg m : (0 : SignSequence.{u}) ≤ m) ha.le
      push_cast
      nlinarith
    · have h := hm b hi
      have hna := mul_nonneg (Nat.cast_nonneg n : (0 : SignSequence.{u}) ≤ n) ha.le
      push_cast
      nlinarith
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, fun b hb => hn b ((growthCoeff_ne_zero_iff_coordinates x b).mpr (Or.inl hb))⟩,
      ⟨n, fun b hb => hn b ((growthCoeff_ne_zero_iff_coordinates x b).mpr (Or.inr hb))⟩⟩

/-- Infinitely lower real monomials are missing from the Gaussian localization as well. -/
theorem real_omegaPower_not_mem_gaussianOmnificMonomialLocalization
    (a : SignSequence.{u}) (ha : 0 < a) :
    ofReal (SignSequence.omegaPower (-(a * SignSequence.ofOrdinal Ordinal.omega0))) ∉
      (gaussianOmnificMonomialLocalizationEmbedding a ha).range := by
  intro h
  exact SignSequence.omegaPower_not_mem_omnificMonomialLocalization a ha
    ((mem_gaussianOmnificMonomialLocalization_iff_coordinates a ha _).mp h).1

/-- The Gaussian monomial localization is a proper subring of the actual complex field. -/
theorem gaussianOmnificMonomialLocalization_range_ne_top (a : SignSequence.{u}) (ha : 0 < a) :
    (gaussianOmnificMonomialLocalizationEmbedding a ha).range ≠ ⊤ := by
  intro h
  apply real_omegaPower_not_mem_gaussianOmnificMonomialLocalization a ha
  rw [h]
  trivial

/-- The Gaussian native localization is a nonzero domain. -/
theorem gaussianOmnificMonomialLocalization_isDomain (a : SignSequence.{u}) (ha : 0 < a) :
    IsDomain (Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha))) :=
  Function.Injective.isDomain (gaussianOmnificMonomialLocalizationEmbedding a ha)
    (gaussianOmnificMonomialLocalizationEmbedding_injective a ha)

/-- The Gaussian native localization is not a field. -/
theorem gaussianOmnificMonomialLocalization_not_isField (a : SignSequence.{u}) (ha : 0 < a) :
    ¬ IsField (Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha))) := by
  intro h
  letI := h.toField
  let b := a * SignSequence.ofOrdinal (Ordinal.omega0 : Ordinal.{u})
  have hb : 0 < b := mul_pos ha (by
    simpa only [Nat.cast_zero] using SignSequence.natCast_lt_omega0.{u} 0)
  apply real_omegaPower_not_mem_gaussianOmnificMonomialLocalization a ha
  refine ⟨(algebraMap _ _ (omnificToGaussian (SignSequence.omnificMonomial b hb)))⁻¹, ?_⟩
  rw [map_inv₀, gaussianOmnificMonomialLocalizationEmbedding_algebraMap,
    gaussianOmnificToSurcomplex_of_omnific, SignSequence.omnificToSurreal_monomial,
    SignSequence.omegaPower_neg, map_inv₀]

/-- The Gaussian monomial localization has no nonzero small unital ring image. -/
theorem gaussianOmnificMonomialLocalization_no_small_ringHom
    (a : SignSequence.{u}) (ha : 0 < a) (S : Type v) [Ring S] [Nontrivial S] [Small.{u} S] :
    ¬ Nonempty (Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha)) →+* S) :=
  gaussianOmnific_localization_no_small_hom _
    (omnificToGaussian_mem_purelyInfinite _ (SignSequence.omnificMonomial_mem_purelyInfinite a ha)) _ S

/-- Every small unital module over the Gaussian monomial localization is trivial. -/
theorem gaussianOmnificMonomialLocalization_small_module
    (a : SignSequence.{u}) (ha : 0 < a) (M : Type v) [AddCommGroup M]
    [Module (Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha))) M]
    [Small.{u} M] : Subsingleton M :=
  gaussianOmnific_localization_small_module _
    (omnificToGaussian_mem_purelyInfinite _ (SignSequence.omnificMonomial_mem_purelyInfinite a ha))
    (Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha))) M

/-- The Gaussian monomial localization is not small in the birthday universe. -/
theorem gaussianOmnificMonomialLocalization_not_small (a : SignSequence.{u}) (ha : 0 < a) :
    ¬ Small.{u} (Localization.Away (omnificToGaussian (SignSequence.omnificMonomial a ha))) := by
  intro hs
  letI := hs
  letI := gaussianOmnificMonomialLocalization_isDomain a ha
  exact gaussianOmnificMonomialLocalization_no_small_ringHom a ha _ ⟨RingHom.id _⟩

end
end Surreal.Surcomplex
