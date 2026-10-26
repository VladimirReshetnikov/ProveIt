import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Arbitrary finite seeds realize every sum when their cardinality acts
surjectively. This does not assert safety of any physical placement. -/
namespace AdditionalSimplifications.SubsetTranslation

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

def translate (s : Finset A) (t : A) : Finset A := s.image (t + ·)

theorem translate_card (s : Finset A) (t : A) : (translate s t).card = s.card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)

theorem translate_sum (s : Finset A) (t : A) :
    (∑ x ∈ translate s t, x) = s.card • t + ∑ x ∈ s, x := by
  rw [translate, Finset.sum_image (fun _ _ _ _ h => add_left_cancel h),
    Finset.sum_add_distrib, Finset.sum_const]

/-- A sum-prescribed translate of an arbitrary seed; no interval formula. -/
theorem exists_translate_sum (s : Finset A)
    (h : Function.Surjective (fun t : A => s.card • t)) (u : A) :
    ∃ t : A, (translate s t).card = s.card ∧ (∑ x ∈ translate s t, x) = u := by
  obtain ⟨t, ht⟩ := h (u - ∑ x ∈ s, x)
  dsimp only at ht
  exact ⟨t, translate_card s t, by rw [translate_sum, ht, sub_add_cancel]⟩

/-- Translation preserves any translation-invariant seed constraint. -/
theorem exists_constrained_subset_sum (s : Finset A) (P : Finset A → Prop)
    (hs : P s) (hP : ∀ s t, P s → P (translate s t))
    (h : Function.Surjective (fun t : A => s.card • t)) (u : A) :
    ∃ S : Finset A, S.card = s.card ∧ (∑ x ∈ S, x) = u ∧ P S := by
  obtain ⟨t, htcard, htsum⟩ := exists_translate_sum s h u
  exact ⟨translate s t, htcard, htsum, hP s t hs⟩

/-- The cyclic-group specialization constructs the coefficient inverse from
coprimality. It includes modulus one, and does not assume a field. -/
theorem exists_zmod_translate_sum {T : ℕ} (s : Finset (ZMod T))
    (h : Nat.Coprime s.card T) (u : ZMod T) :
    ∃ t : ZMod T, (translate s t).card = s.card ∧
      (∑ x ∈ translate s t, x) = u := by
  apply exists_translate_sum s ?_ u
  intro v
  refine ⟨(((ZMod.unitOfCoprime s.card h)⁻¹ : (ZMod T)ˣ) : ZMod T) * v, ?_⟩
  simpa only [nsmul_eq_mul, ZMod.coe_unitOfCoprime] using
    Units.mul_inv_cancel_left (ZMod.unitOfCoprime s.card h) v

-- A deliberately non-interval seed: cardinality three is a unit modulo eight.
example (u : ZMod 8) : ∃ t : ZMod 8,
    (translate ({0, 2, 5} : Finset (ZMod 8)) t).card = 3 ∧
    (∑ x ∈ translate ({0, 2, 5} : Finset (ZMod 8)) t, x) = u := by
  have h := exists_zmod_translate_sum ({0, 2, 5} : Finset (ZMod 8)) (by decide) u
  have hc : ({0, 2, 5} : Finset (ZMod 8)).card = 3 := by decide
  simpa only [hc] using h

#print axioms exists_translate_sum
#print axioms exists_constrained_subset_sum
#print axioms exists_zmod_translate_sum

end AdditionalSimplifications.SubsetTranslation
