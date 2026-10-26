import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Card

/-!
Existence-only alternate interface for ControllerIntervalSums.
The finite seed is translated; no triangular-number formula or division
by 2 is needed. Exact old startFor/targetInterval definitions are not changed.
-/
namespace ControllerSubsetTranslation
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def translate (s : Finset G) (t : G) : Finset G :=
  s.image (fun x => x+t)

theorem translate_card (s : Finset G) (t : G) :
    (translate s t).card = s.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

theorem translate_sum (s : Finset G) (t : G) :
    (∑ x ∈ translate s t, x) = (∑ x ∈ s, x)+s.card • t := by
  rw [translate, Finset.sum_image (fun _ _ _ _ h => add_right_cancel h),
    Finset.sum_add_distrib, Finset.sum_const]

/-- The mathematical core is the surjectivity of multiplication by card S. -/
theorem exists_translate_sum (s : Finset G) (u : G)
    (hmul : Function.Surjective (fun t : G => s.card • t)) :
    ∃ t : G, (translate s t).card = s.card ∧
      (∑ x ∈ translate s t, x) = u := by
  obtain ⟨t, ht⟩ := hmul (u-∑ x ∈ s, x)
  change s.card • t = u-∑ x ∈ s, x at ht
  refine ⟨t, translate_card s t, ?_⟩
  rw [translate_sum, ht, add_comm]
  exact sub_add_cancel _ _

/-- A chosen cardinality coprime to T makes translation reach every sum. -/
theorem zmod_nsmul_surjective {T a : ℕ} (h : Nat.Coprime a T) :
    Function.Surjective (fun t : ZMod T => a • t) := by
  intro u
  refine ⟨(((ZMod.unitOfCoprime a h)⁻¹ : (ZMod T)ˣ) : ZMod T)*u, ?_⟩
  change a • _ = u
  rw [nsmul_eq_mul]
  change (ZMod.unitOfCoprime a h : ZMod T) *
    ((((ZMod.unitOfCoprime a h)⁻¹ : (ZMod T)ˣ) : ZMod T)*u) = u
  exact Units.mul_inv_cancel_left _ _

/-- Any seed of the right cardinality is sufficient, regardless of shape. -/
theorem exists_seed_translate {T a : ℕ} (s : Finset (ZMod T))
    (hs : s.card = a) (h : Nat.Coprime a T) (u : ZMod T) :
    ∃ t : ZMod T, (translate s t).card = a ∧
      (∑ x ∈ translate s t, x) = u := by
  simpa only [hs] using exists_translate_sum s u
    (by simpa only [hs] using zmod_nsmul_surjective h)

/-- For clients requiring only existence, choosing a finite subset by
cardinality replaces all interval and triangular-number calculations. -/
theorem exists_subset_card_sum {T : ℕ} [NeZero T]
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    ∃ s : Finset (ZMod T), s.card = a ∧ (∑ x ∈ s, x) = u := by
  have hcard : a ≤ (Finset.univ : Finset (ZMod T)).card := by
    simpa only [Finset.card_univ, ZMod.card] using ha
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨t, ht, hu⟩ := exists_seed_translate s hs h u
  exact ⟨translate s t, ht, hu⟩

-- Even modulus, wrap-around, zero-ring edge and non-interval seed.
example : ∃ s : Finset (ZMod 8), s.card = 3 ∧ (∑ x ∈ s, x) = 7 :=
  exists_subset_card_sum 3 (by decide) (by decide) 7
example : ∃ s : Finset (ZMod 1), s.card = 0 ∧ (∑ x ∈ s, x) = 0 :=
  exists_subset_card_sum 0 (by decide) (by decide) 0
example (u : ZMod 8) : ∃ t : ZMod 8,
    (translate {0, 2, 5} t).card = 3 ∧ (∑ x ∈ translate {0, 2, 5} t, x) = u :=
  exists_seed_translate {0, 2, 5} (by decide) (by decide) u

#print axioms exists_translate_sum
#print axioms exists_subset_card_sum
end ControllerSubsetTranslation
