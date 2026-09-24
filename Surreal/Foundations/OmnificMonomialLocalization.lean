import Surreal.Surcomplex.OmnificUnitObstruction

/-!
# Localization at a positive real monomial

The actual real instance of `osq:prop:locsupport`. The native localization
embeds in the surreal field; its image consists exactly of normal forms
bounded below by a negative natural multiple of the chosen exponent.
It is a nonzero domain, a proper subring of the field, and is not a field.
The target and module obstructions are supplied by OmnificUnitObstruction.
-/

universe u v
namespace Surreal.Foundations.SignSequence
open SmallNormalForm
noncomputable section

/-- The canonical map from native monomial localization to the actual surreal field. -/
def omnificMonomialLocalizationEmbedding (a : SignSequence.{u}) (ha : 0 < a) :
    Localization.Away (omnificMonomial a ha) →+* SignSequence.{u} :=
  IsLocalization.Away.lift (omnificMonomial a ha)
    (g := omnificToSurreal) (isUnit_iff_ne_zero.mpr (omegaPower_ne_zero a))

@[simp] theorem omnificMonomialLocalizationEmbedding_algebraMap
    (a : SignSequence.{u}) (ha : 0 < a) (f : OmnificInteger.{u}) :
    omnificMonomialLocalizationEmbedding a ha
      (algebraMap _ (Localization.Away (omnificMonomial a ha)) f) = omnificToSurreal f := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The native localization embeds in the actual field. -/
theorem omnificMonomialLocalizationEmbedding_injective (a : SignSequence.{u}) (ha : 0 < a) :
    Function.Injective (omnificMonomialLocalizationEmbedding a ha) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (omnificMonomial a ha)) _).mpr
  intro x y
  simp only [omnificMonomialLocalizationEmbedding_algebraMap]
  constructor
  · intro h
    simpa only [omnificMonomialLocalizationEmbedding_algebraMap] using
      congrArg (omnificMonomialLocalizationEmbedding a ha) h
  · intro h
    exact congrArg _ (omnificToSurreal_injective h)

/-- The image consists precisely of fractions with a power of the chosen monomial denominator. -/
theorem mem_omnificMonomialLocalization_range_iff (a : SignSequence.{u}) (ha : 0 < a)
    (x : SignSequence.{u}) :
    x ∈ (omnificMonomialLocalizationEmbedding a ha).range ↔
      ∃ (n : ℕ) (f : OmnificInteger.{u}), x * omegaPower (n * a) = omnificToSurreal f := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨n, f, h⟩ := IsLocalization.Away.surj (omnificMonomial a ha) z
    refine ⟨n, f, ?_⟩
    have he := congrArg (omnificMonomialLocalizationEmbedding a ha) h
    simpa only [map_mul, map_pow, omnificMonomialLocalizationEmbedding_algebraMap,
      omnificToSurreal_monomial, omegaPower_nat_mul] using he
  · rintro ⟨n, f, h⟩
    let z := IsLocalization.mk' (Localization.Away (omnificMonomial a ha)) f
      (⟨omnificMonomial a ha ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (omnificMonomial a ha))
    refine ⟨z, ?_⟩
    apply mul_right_cancel₀ (omegaPower_ne_zero (n * a))
    rw [h, omegaPower_nat_mul]
    have he := congrArg (omnificMonomialLocalizationEmbedding a ha)
      (IsLocalization.mk'_spec (Localization.Away (omnificMonomial a ha)) f
        (⟨omnificMonomial a ha ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (omnificMonomial a ha)))
    simpa only [map_mul, map_pow, omnificMonomialLocalizationEmbedding_algebraMap,
      omnificToSurreal_monomial] using he

/-- Support bounded below by a natural multiple is the exact localization membership criterion. -/
theorem mem_omnificMonomialLocalization_iff_support (a : SignSequence.{u}) (ha : 0 < a)
    (x : SignSequence.{u}) :
    x ∈ (omnificMonomialLocalizationEmbedding a ha).range ↔
      ∃ n : ℕ, ∀ b ∈ support (normalForm x), -(n * a) ≤ b := by
  rw [mem_omnificMonomialLocalization_range_iff]
  constructor
  · rintro ⟨n, f, h⟩
    refine ⟨n, ?_⟩
    have hx : x = omegaPower (-(n * a)) * omnificToSurreal f := by
      rw [← h, mul_comm x, ← mul_assoc, omegaPower_neg,
        inv_mul_cancel₀ (omegaPower_ne_zero _), _root_.one_mul]
    intro b hb
    rw [hx] at hb
    obtain ⟨c, hc, rfl⟩ := support_omegaPower_mul_subset _ _ hb
    have hc0 : 0 ≤ c := by
      by_contra hn
      exact hc ((mem_nonnegativeSupportSubring_iff _).mp f.val.property c (lt_of_not_ge hn))
    linarith
  · rintro ⟨n, h⟩
    obtain ⟨f, _, hf⟩ := exists_purelyInfinite_of_support_pos (omegaPower ((n + 1) * a) * x) (by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := support_omegaPower_mul_subset _ _ hb
      have hc0 := h c hc
      have hn : ((n : SignSequence.{u}) + 1) * a = n * a + a := by ring
      rw [hn]
      linarith)
    refine ⟨n + 1, f, ?_⟩
    rw [hf, Nat.cast_add_one, mul_comm]

/-- Inverting a positive monomial brings every ordinary real coefficient into the ring. -/
theorem ofReal_mem_omnificMonomialLocalization (a : SignSequence.{u}) (ha : 0 < a) (r : ℝ) :
    ofReal r ∈ (omnificMonomialLocalizationEmbedding a ha).range := by
  rw [mem_omnificMonomialLocalization_iff_support]
  refine ⟨0, fun b hb => ?_⟩
  have hb0 : b = 0 := by
    by_contra hn
    exact hb (by rw [normalForm_ofReal, coeff_single, if_neg hn])
  simp only [Nat.cast_zero, zero_mul, neg_zero, hb0, le_refl]

/-- Inverses at an infinitely larger exponent are absent from this localization. -/
theorem omegaPower_not_mem_omnificMonomialLocalization (a : SignSequence.{u}) (ha : 0 < a) :
    omegaPower (-(a * ofOrdinal Ordinal.omega0)) ∉
      (omnificMonomialLocalizationEmbedding a ha).range := by
  rw [mem_omnificMonomialLocalization_iff_support]
  rintro ⟨n, hn⟩
  have h := hn (-(a * ofOrdinal Ordinal.omega0)) (by
    change coeff (normalForm (omegaPower _)) _ ≠ 0
    rw [normalForm_omegaPower, coeff_single, if_pos rfl]
    exact _root_.one_ne_zero)
  have hlarge := mul_lt_mul_of_pos_left (natCast_lt_omega0.{u} n) ha
  nlinarith

/-- Adjoining a single monomial inverse gives a proper subring of the surreal field. -/
theorem omnificMonomialLocalization_range_ne_top (a : SignSequence.{u}) (ha : 0 < a) :
    (omnificMonomialLocalizationEmbedding a ha).range ≠ ⊤ := by
  intro h
  apply omegaPower_not_mem_omnificMonomialLocalization a ha
  rw [h]
  trivial

/-- The native monomial localization is a nonzero domain. -/
theorem omnificMonomialLocalization_isDomain (a : SignSequence.{u}) (ha : 0 < a) :
    IsDomain (Localization.Away (omnificMonomial a ha)) :=
  Function.Injective.isDomain (omnificMonomialLocalizationEmbedding a ha)
    (omnificMonomialLocalizationEmbedding_injective a ha)

/-- The missing inverse of an infinitely larger positive monomial rules out field structure. -/
theorem omnificMonomialLocalization_not_isField (a : SignSequence.{u}) (ha : 0 < a) :
    ¬ IsField (Localization.Away (omnificMonomial a ha)) := by
  intro h
  letI := h.toField
  let b := a * ofOrdinal (Ordinal.omega0 : Ordinal.{u})
  have hb : 0 < b := mul_pos ha (by simpa only [Nat.cast_zero] using natCast_lt_omega0.{u} 0)
  apply omegaPower_not_mem_omnificMonomialLocalization a ha
  refine ⟨(algebraMap _ (Localization.Away (omnificMonomial a ha)) (omnificMonomial b hb))⁻¹, ?_⟩
  rw [map_inv₀, omnificMonomialLocalizationEmbedding_algebraMap,
    omnificToSurreal_monomial, omegaPower_neg]

/-- No nonzero small ring can receive a unital map from the monomial localization. -/
theorem omnificMonomialLocalization_no_small_ringHom (a : SignSequence.{u}) (ha : 0 < a)
    (S : Type v) [Ring S] [Nontrivial S] [Small.{u} S] :
    ¬ Nonempty (Localization.Away (omnificMonomial a ha) →+* S) :=
  omnific_localization_no_small_hom _ (omnificMonomial_mem_purelyInfinite a ha) _ S

/-- Every small unital module over this nonzero domain is trivial. -/
theorem omnificMonomialLocalization_small_module (a : SignSequence.{u}) (ha : 0 < a)
    (M : Type v) [AddCommGroup M] [Module (Localization.Away (omnificMonomial a ha)) M]
    [Small.{u} M] : Subsingleton M :=
  omnific_localization_small_module _ (omnificMonomial_mem_purelyInfinite a ha)
    (Localization.Away (omnificMonomial a ha)) M

/-- A monomial localization is not small in the surreal birthday universe. -/
theorem omnificMonomialLocalization_not_small (a : SignSequence.{u}) (ha : 0 < a) :
    ¬ Small.{u} (Localization.Away (omnificMonomial a ha)) := by
  intro hs
  letI := hs
  letI := omnificMonomialLocalization_isDomain a ha
  exact omnificMonomialLocalization_no_small_ringHom a ha _ ⟨RingHom.id _⟩

end
end Surreal.Foundations.SignSequence
