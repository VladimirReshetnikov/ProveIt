import Surreal.Algebra.CoefficientPullback
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction-field inclusion of an augmentation ring

The algebraic mechanism of `odg:def:lem:ainfrac`: one nonzero element
of the augmentation kernel clears every element into the coefficient
pullback. No assumption on surjectivity of the augmentation is needed.
-/

namespace Surreal.AugmentationFractionField

noncomputable section

variable {F K O : Type*} [Field F] [CommRing K] [CommRing O]
  (A : Subring F) (ε : A →+* K) (i : O →+* K)

/-- Inclusion of the coefficient pullback into the ambient field. -/
def inclusion : CoefficientPullback.subring ε i →+* F :=
  A.subtype.comp (CoefficientPullback.subring ε i).subtype

theorem inclusion_injective : Function.Injective (inclusion A ε i) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

/-- The native fraction field of the pullback embeds into the ambient field. -/
def fractionEmbedding : FractionRing (CoefficientPullback.subring ε i) →+* F :=
  IsFractionRing.lift (inclusion_injective A ε i)

@[simp] theorem fractionEmbedding_algebraMap (a : CoefficientPullback.subring ε i) :
    fractionEmbedding A ε i (algebraMap _ (FractionRing _) a) = a.val.val :=
  IsFractionRing.lift_algebraMap _ _

/-- A nonzero kernel element clears every element into the pullback, with kernel numerator. -/
theorem exists_kernel_fraction (d : A) (hd : ε d = 0) (hd0 : d ≠ 0) (a : A) :
    ∃ s t : CoefficientPullback.subring ε i,
      t ≠ 0 ∧ ε s.val = 0 ∧ ε t.val = 0 ∧ a.val = s.val.val / t.val.val := by
  have ha : ε (a * d) = 0 := by rw [map_mul, hd, mul_zero]
  let s : CoefficientPullback.subring ε i := ⟨a * d, ⟨0, by rw [map_zero, ha]⟩⟩
  let t : CoefficientPullback.subring ε i := ⟨d, ⟨0, by rw [map_zero, hd]⟩⟩
  have hd' : d.val ≠ 0 := fun h => hd0 (Subtype.ext h)
  refine ⟨s, t, fun h => hd0 (congrArg Subtype.val h), ha, hd, ?_⟩
  exact (mul_div_cancel_right₀ a.val hd').symm

/-- The support ring lies in the native pullback fraction field whenever the kernel is nonzero. -/
theorem mem_fractionField (d : A) (hd : ε d = 0) (hd0 : d ≠ 0) (a : A) :
    a.val ∈ (fractionEmbedding A ε i).fieldRange := by
  obtain ⟨s, t, _, _, _, he⟩ := exists_kernel_fraction A ε i d hd hd0 a
  refine ⟨algebraMap _ (FractionRing _) s / algebraMap _ (FractionRing _) t, ?_⟩
  simpa only [map_div₀, fractionEmbedding_algebraMap] using he.symm

end
end Surreal.AugmentationFractionField
