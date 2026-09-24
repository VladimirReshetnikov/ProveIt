import Surreal.Foundations.OmnificConstantRigidity
import Surreal.Foundations.SmallNormalFormProductFrontier
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Small-family monomial divisors and denominator clearing

The set-sized bounds `odg:lem:setbounds`, common monomial divisibility
`odg:thm:commondivisor`, and global clearing `odg:thm:fractions`.
The actual sign field has lower-universe-small normal-form supports.
Families are explicitly small in that same universe; their union of
supports therefore admits new surreal bounds, without requiring those
bounds to belong to a previously fixed Hahn workspace.
-/

universe u v
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- Every small positive family has a positive strict lower bound, including an empty family. -/
theorem small_positive_exponent_bound {ι : Type v} [Small.{u} ι]
    (e : ι → SignSequence.{u}) (he : ∀ i, 0 < e i) :
    ∃ δ : SignSequence.{u}, 0 < δ ∧ ∀ i, δ < e i := by
  obtain ⟨δ, hδ, h⟩ := exists_positive_lower_bound (Shrink.{u} ι)
    (fun i => e ((equivShrink ι).symm i)) (fun i => he _)
  exact ⟨δ, hδ, fun i => by simpa only [Equiv.symm_apply_apply] using h (equivShrink ι i)⟩

/-- Every small family of exponents has a strict upper bound, including an empty family. -/
theorem small_upper_exponent_bound {ι : Type v} [Small.{u} ι]
    (e : ι → SignSequence.{u}) : ∃ h : SignSequence.{u}, ∀ i, e i < h := by
  obtain ⟨h, hh⟩ := small_strict_upper_bounds (Shrink.{u} ι)
    (fun i => e ((equivShrink ι).symm i))
  exact ⟨h, fun i => by simpa only [Equiv.symm_apply_apply] using hh (equivShrink ι i)⟩

/-- A surreal with strictly positive growth support is an actual purely infinite omnific integer. -/
theorem exists_purelyInfinite_of_support_pos (x : SignSequence.{u})
    (hx : ∀ a ∈ support (normalForm x), 0 < a) :
    ∃ z : OmnificInteger.{u}, z ∈ omnificPurelyInfiniteIdeal ∧ omnificToSurreal z = x := by
  have hc : coeff (normalForm x) 0 = 0 := by
    by_contra h
    exact (lt_irrefl (0 : SignSequence.{u})) (hx 0 h)
  obtain ⟨z, hz⟩ := (exists_omnific_iff x).mpr ⟨fun a ha => by
    by_contra h
    exact (not_lt_of_ge (hx a h).le) ha, ⟨0, by simpa only [Int.cast_zero] using hc.symm⟩⟩
  refine ⟨z, ?_, hz⟩
  rw [mem_omnificPurelyInfiniteIdeal_iff, hz]
  exact hx

/-- Multiplication by a Conway monomial shifts every supported growth exponent. -/
theorem support_omegaPower_mul_subset (a x : SignSequence.{u})
    {b : SignSequence.{u}} (hb : b ∈ support (normalForm (omegaPower a * x))) :
    ∃ c ∈ support (normalForm x), a + c = b := by
  rw [normalForm_mul, normalForm_omegaPower] at hb
  obtain ⟨d, hd, c, hc, hdc⟩ := exists_add_eq_of_mem_support_mul _ _ hb
  have hda : d = a := by
    by_contra h
    simp only [mem_support, coeff_single, if_neg h, ne_eq, not_true_eq_false] at hd
  exact ⟨c, hc, hda ▸ hdc⟩

/-- A single positive monomial divides an entire small family, with purely infinite quotients. -/
theorem omnific_common_monomial_divisor {ι : Type v} [Small.{u} ι]
    (s : ι → OmnificInteger.{u}) (hs : ∀ i, s i ∈ omnificPurelyInfiniteIdeal) :
    ∃ (δ : SignSequence.{u}) (hδ : 0 < δ), ∀ i,
      ∃ q ∈ omnificPurelyInfiniteIdeal, s i = omnificMonomial δ hδ * q := by
  let E : Set SignSequence.{u} := ⋃ i, support (normalForm (omnificToSurreal (s i)))
  have hE : ∀ a : E, 0 < a.val := by
    rintro ⟨a, ha⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact (mem_omnificPurelyInfiniteIdeal_iff (s i)).mp (hs i) a hi
  obtain ⟨δ, hδ, hb⟩ := small_positive_exponent_bound (fun a : E => a.val) hE
  refine ⟨δ, hδ, fun i => ?_⟩
  obtain ⟨q, hq, he⟩ := exists_purelyInfinite_of_support_pos
    (omegaPower (-δ) * omnificToSurreal (s i)) (by
      intro b hb'
      obtain ⟨c, hc, rfl⟩ := support_omegaPower_mul_subset _ _ hb'
      have hδc := hb ⟨c, Set.mem_iUnion.mpr ⟨i, hc⟩⟩
      exact neg_lt_iff_pos_add.mp (neg_lt_neg hδc))
  refine ⟨q, hq, ?_⟩
  apply omnificToSurreal_injective
  rw [map_mul, omnificToSurreal_monomial, he, omegaPower_neg,
    ← mul_assoc, mul_inv_cancel₀ (omegaPower_ne_zero δ), one_mul]

/-- In field notation the common monomial quotients are exactly division by that monomial. -/
theorem omnific_common_monomial_quotients {ι : Type v} [Small.{u} ι]
    (s : ι → OmnificInteger.{u}) (hs : ∀ i, s i ∈ omnificPurelyInfiniteIdeal) :
    ∃ (δ : SignSequence.{u}) (hδ : 0 < δ), ∀ i,
      omnificMonomial δ hδ ∣ s i ∧ ∃ q ∈ omnificPurelyInfiniteIdeal,
        omnificToSurreal q = omnificToSurreal (s i) / omegaPower δ := by
  obtain ⟨δ, hδ, h⟩ := omnific_common_monomial_divisor s hs
  refine ⟨δ, hδ, fun i => ?_⟩
  obtain ⟨q, hq, he⟩ := h i
  refine ⟨⟨q, he⟩, q, hq, ?_⟩
  rw [he, map_mul, omnificToSurreal_monomial, mul_div_cancel_left₀ _ (omegaPower_ne_zero δ)]

/-- One positive monomial clears every member of a small family into the purely infinite ideal. -/
theorem omnific_monomial_clearing {ι : Type v} [Small.{u} ι] (s : ι → SignSequence.{u}) :
    ∃ h : SignSequence.{u}, 0 < h ∧ ∀ i,
      ∃ z ∈ omnificPurelyInfiniteIdeal, omnificToSurreal z = omegaPower h * s i := by
  let E : Set SignSequence.{u} := ⋃ i, support (normalForm (s i))
  obtain ⟨b, hb⟩ := small_upper_exponent_bound (fun a : E => -a.val)
  let h := max b 0 + 1
  have hh : 0 < h := lt_of_le_of_lt (le_max_right b 0) (lt_add_one _)
  refine ⟨h, hh, fun i => exists_purelyInfinite_of_support_pos _ ?_⟩
  intro a ha
  obtain ⟨c, hc, rfl⟩ := support_omegaPower_mul_subset _ _ ha
  have hcb := hb ⟨c, Set.mem_iUnion.mpr ⟨i, hc⟩⟩
  have hch : -c < h := hcb.trans (lt_of_le_of_lt (le_max_left b 0) (lt_add_one _))
  exact neg_lt_iff_pos_add.mp hch

/-- Every actual surreal is a fraction of two purely infinite omnific integers. -/
theorem surreal_eq_omnific_fraction (x : SignSequence.{u}) :
    ∃ a b : OmnificInteger.{u}, a ∈ omnificPurelyInfiniteIdeal ∧
      b ∈ omnificPurelyInfiniteIdeal ∧ b ≠ 0 ∧
      x = omnificToSurreal a / omnificToSurreal b := by
  obtain ⟨h, hh, hs⟩ := omnific_monomial_clearing (fun _ : PUnit => x)
  obtain ⟨a, ha, he⟩ := hs PUnit.unit
  refine ⟨a, omnificMonomial h hh, ha, omnificMonomial_mem_purelyInfinite h hh,
    omnificMonomial_ne_zero h hh, ?_⟩
  rw [he, omnificToSurreal_monomial, mul_div_cancel_left₀ _ (omegaPower_ne_zero h)]

/-- The actual surreal field is an algebra over its omnific subring by the canonical inclusion. -/
instance omnificSurrealAlgebra : Algebra OmnificInteger.{u} SignSequence.{u} :=
  omnificToSurreal.toAlgebra

/-- The omnific scalar action is faithful because the canonical inclusion is injective. -/
instance omnificSurrealFaithfulSMul : FaithfulSMul OmnificInteger.{u} SignSequence.{u} :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr omnificToSurreal_injective

/-- The constructed surreal field is a field of fractions of the actual omnific ring. -/
instance omnificSurrealIsFractionRing : IsFractionRing OmnificInteger.{u} SignSequence.{u} := by
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _, _, _, h⟩ := surreal_eq_omnific_fraction x
  exact ⟨a, b, h⟩

/-- Every purely infinite omnific integer is a nonunit. -/
theorem omnific_not_isUnit_of_purelyInfinite (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) : ¬ IsUnit x := by
  intro hu
  have h := hu.map omnificConstantCoeff
  change omnificConstantCoeff x = 0 at hx
  rw [hx] at h
  exact not_isUnit_zero h

/-- A nonzero purely infinite element factors into two nonzero purely infinite nonunits. -/
theorem omnific_purelyInfinite_factorization (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hx0 : x ≠ 0) :
    ∃ a b : OmnificInteger.{u}, a ∈ omnificPurelyInfiniteIdeal ∧
      b ∈ omnificPurelyInfiniteIdeal ∧ a ≠ 0 ∧ b ≠ 0 ∧
      ¬ IsUnit a ∧ ¬ IsUnit b ∧ x = a * b := by
  obtain ⟨δ, hδ, h⟩ := omnific_common_monomial_divisor (fun _ : PUnit => x) (fun _ => hx)
  obtain ⟨q, hq, he⟩ := h PUnit.unit
  refine ⟨omnificMonomial δ hδ, q, omnificMonomial_mem_purelyInfinite _ _, hq,
    omnificMonomial_ne_zero _ _, ?_,
    omnific_not_isUnit_of_purelyInfinite _ (omnificMonomial_mem_purelyInfinite _ _),
    omnific_not_isUnit_of_purelyInfinite q hq, he⟩
  intro hq0
  rw [hq0, mul_zero] at he
  exact hx0 he

end
end Surreal.Foundations.SignSequence
