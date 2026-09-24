import Surreal.HahnSeries.QuadraticIdealDefinition
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The support ring as multipliers of the purely infinite ideal

The Hahn assertions of `odg:def:lem:ainfrac`, `odg:def:thm:multiplier`,
and `odg:def:eq:multiplier`. A forbidden positive t-exponent is exposed
by shifting it to zero with a single negative monomial.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CommRing O]

/-- The actual image of the purely infinite ideal in the ambient Hahn field. -/
def PurelyInfiniteSeries (f : K⟦Γ⟧) : Prop := ∀ a, 0 ≤ a → f.coeff a = 0

theorem purelyInfiniteSeries_iff (f : nonpositiveSupportSubring Γ K) :
    PurelyInfiniteSeries f.val ↔ f ∈ purelyInfiniteIdeal := by
  change (∀ a, 0 ≤ a → f.val.coeff a = 0) ↔ f.val.coeff 0 = 0
  constructor
  · exact fun h => h 0 le_rfl
  · intro h a ha
    rcases eq_or_lt_of_le ha with h₀ | h₀
    · simpa only [← h₀] using h
    · exact f.property a h₀

theorem PurelyInfiniteSeries.mem_supportRing {f : K⟦Γ⟧} (hf : PurelyInfiniteSeries f) :
    f ∈ nonpositiveSupportSubring Γ K := fun a ha => hf a ha.le

omit [IsOrderedAddMonoid Γ] in
/-- Every negative monomial is purely infinite, without any discreteness assumption. -/
theorem purelyInfiniteSeries_single (g : Γ) (hg : g < 0) (c : K) :
    PurelyInfiniteSeries (single g c) := by
  intro a ha
  rw [coeff_single_of_ne (ne_of_gt (hg.trans_le ha))]

/-- The ambient multiplier condition on the actual purely infinite ideal. -/
def IsPurelyInfiniteMultiplier (f : K⟦Γ⟧) : Prop :=
  ∀ x : K⟦Γ⟧, PurelyInfiniteSeries x → PurelyInfiniteSeries (f * x)

/-- The multiplier identity holds even in the full ambient Hahn field. -/
theorem purelyInfiniteMultiplier_iff (f : K⟦Γ⟧) :
    IsPurelyInfiniteMultiplier f ↔ f ∈ nonpositiveSupportSubring Γ K := by
  constructor
  · intro hf a ha
    have h := hf (single (-a) 1) (purelyInfiniteSeries_single (-a) (neg_neg_of_pos ha) 1) 0 le_rfl
    simpa only [coeff_mul_single, zero_sub, neg_neg, mul_one] using h
  · intro hf x hx
    let f' : nonpositiveSupportSubring Γ K := ⟨f, hf⟩
    let x' : nonpositiveSupportSubring Γ K := ⟨x, hx.mem_supportRing⟩
    exact (purelyInfiniteSeries_iff (f' * x')).mpr
      (Ideal.mul_mem_left purelyInfiniteIdeal f' ((purelyInfiniteSeries_iff x').mp hx))

/-- Multipliers and their inverses recover precisely the nonzero coefficient constants. -/
theorem coefficient_iff_multiplier_and_inverse (f : K⟦Γ⟧) :
    (∃ c : K, f = C c) ↔
      f = 0 ∨ (f ≠ 0 ∧ IsPurelyInfiniteMultiplier f ∧ IsPurelyInfiniteMultiplier f⁻¹) := by
  constructor
  · rintro ⟨c, rfl⟩
    by_cases hc : c = 0
    · left; simp [hc]
    · right
      refine ⟨by simpa using hc, (purelyInfiniteMultiplier_iff _).mpr (nonpositiveConstants c).property,
        (purelyInfiniteMultiplier_iff _).mpr ?_⟩
      rw [← map_inv₀ C]
      exact (nonpositiveConstants c⁻¹).property
  · rintro (rfl | ⟨hf, hm, hi⟩)
    · exact ⟨0, (map_zero C).symm⟩
    · let a : nonpositiveSupportSubring Γ K := ⟨f, (purelyInfiniteMultiplier_iff f).mp hm⟩
      let b : nonpositiveSupportSubring Γ K := ⟨f⁻¹, (purelyInfiniteMultiplier_iff _).mp hi⟩
      have hab : a * b = 1 := Subtype.ext (mul_inv_cancel₀ hf)
      have hu : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b, hab⟩
      exact ⟨nonpositiveConstantCoeff a, congrArg Subtype.val (nonpositiveSupport_unit_eq_constant a hu)⟩

/-- The canonical inclusion of a coefficient-restricted ring into its Hahn field. -/
def coefficientRestrictedHahnInclusion (i : O →+* K) :
    coefficientRestrictedSubring (Γ := Γ) i →+* K⟦Γ⟧ :=
  (nonpositiveSupportSubring Γ K).subtype.comp (coefficientRestrictedSubring i).subtype

theorem coefficientRestrictedHahnInclusion_injective (i : O →+* K) :
    Function.Injective (coefficientRestrictedHahnInclusion (Γ := Γ) i) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

/-- The native fraction field, embedded faithfully into the Hahn field. -/
def coefficientRestrictedFractionEmbedding (i : O →+* K) :
    FractionRing (coefficientRestrictedSubring (Γ := Γ) i) →+* K⟦Γ⟧ :=
  IsFractionRing.lift (coefficientRestrictedHahnInclusion_injective i)

@[simp] theorem coefficientRestrictedFractionEmbedding_algebraMap (i : O →+* K)
    (a : coefficientRestrictedSubring (Γ := Γ) i) :
    coefficientRestrictedFractionEmbedding i (algebraMap _ (FractionRing _) a) = a.val.val :=
  IsFractionRing.lift_algebraMap _ _

/-- Every purely infinite series belongs to each full coefficient pullback. -/
def purelyInfiniteRestricted (i : O →+* K) (f : K⟦Γ⟧) (hf : PurelyInfiniteSeries f) :
    coefficientRestrictedSubring (Γ := Γ) i :=
  ⟨⟨f, hf.mem_supportRing⟩, ⟨0, by rw [map_zero]; exact (hf 0 le_rfl).symm⟩⟩

/-- A fixed negative monomial clears every support-ring element into the purely infinite ideal. -/
theorem nonpositiveSupport_fraction_of_monomial (i : O →+* K)
    (g : Γ) (hg : g < 0) (f : nonpositiveSupportSubring Γ K) :
    ∃ a b : coefficientRestrictedSubring (Γ := Γ) i, b ≠ 0 ∧
      PurelyInfiniteSeries a.val.val ∧ PurelyInfiniteSeries b.val.val ∧
      f.val = a.val.val / b.val.val := by
  have hb := purelyInfiniteSeries_single g hg (1 : K)
  have ha := (purelyInfiniteMultiplier_iff f.val).mpr f.property _ hb
  let a := purelyInfiniteRestricted i (f.val * single g 1) ha
  let b := purelyInfiniteRestricted i (single g 1) hb
  have hb0 : (single g 1 : K⟦Γ⟧) ≠ 0 := by simp
  refine ⟨a, b, ?_, ha, hb, ?_⟩
  · intro h
    exact hb0 (congrArg (coefficientRestrictedHahnInclusion i) h)
  · exact (mul_div_cancel_right₀ f.val hb0).symm

/-- The support ring is contained in the embedded native fraction field when Γ is nontrivial. -/
theorem nonpositiveSupport_mem_fractionField [Nontrivial Γ] (i : O →+* K)
    (f : nonpositiveSupportSubring Γ K) :
    f.val ∈ (coefficientRestrictedFractionEmbedding i).fieldRange := by
  obtain ⟨g, hg⟩ := exists_lt (0 : Γ)
  obtain ⟨a, b, _, _, _, he⟩ := nonpositiveSupport_fraction_of_monomial i g hg f
  refine ⟨algebraMap _ (FractionRing _) a / algebraMap _ (FractionRing _) b, ?_⟩
  simpa only [map_div₀, coefficientRestrictedFractionEmbedding_algebraMap] using he.symm

/-- The multiplier identity restricted to the source's interpreted fraction field. -/
theorem fraction_multiplier_iff (i : O →+* K)
    (f : FractionRing (coefficientRestrictedSubring (Γ := Γ) i)) :
    IsPurelyInfiniteMultiplier (coefficientRestrictedFractionEmbedding i f) ↔
      coefficientRestrictedFractionEmbedding i f ∈ nonpositiveSupportSubring Γ K :=
  purelyInfiniteMultiplier_iff _

end
end Surreal.HahnSeries
