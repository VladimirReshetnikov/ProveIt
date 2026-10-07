import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev MissingAssignment (s : ℕ) := {v : Fin s → Fin s // ¬Function.Surjective v}

def assignmentSplitMap (s : ℕ) : Equiv.Perm (Fin s) ⊕ MissingAssignment s → (Fin s → Fin s)
  | Sum.inl e => e
  | Sum.inr v => v.val

theorem assignmentSplitMap_bijective (s : ℕ) : Function.Bijective (assignmentSplitMap s) := by
  classical
  constructor
  · intro a b h
    rcases a with a | a <;> rcases b with b | b
    · apply congrArg Sum.inl
      exact Equiv.ext (congrFun h)
    · exfalso
      apply b.property
      change (a : Fin s → Fin s) = b.val at h
      exact h ▸ a.surjective
    · exfalso
      apply a.property
      change a.val = (b : Fin s → Fin s) at h
      exact h.symm ▸ b.surjective
    · apply congrArg Sum.inr
      exact Subtype.ext h
  · intro v
    by_cases hv : Function.Surjective v
    · exact ⟨Sum.inl (Equiv.ofBijective v (Finite.surjective_iff_bijective.mp hv)), rfl⟩
    · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩

noncomputable def assignmentSplitEquiv (s : ℕ) :
    Equiv.Perm (Fin s) ⊕ MissingAssignment s ≃ (Fin s → Fin s) :=
  Equiv.ofBijective (assignmentSplitMap s) (assignmentSplitMap_bijective s)

theorem missingAssignment_coordinate {s : ℕ} (v : MissingAssignment s) :
    ∃ j : Fin s, ∀ i : Fin s, v.val i ≠ j := by
  classical
  have h := v.property
  simpa only [Function.Surjective, not_forall, not_exists] using h

theorem assignmentSplit_card (s : ℕ) :
    s.factorial + Fintype.card (MissingAssignment s) = s ^ s := by
  classical
  have h := Fintype.card_congr (assignmentSplitEquiv s)
  simpa only [Fintype.card_sum, Fintype.card_perm, Fintype.card_fun, Fintype.card_fin] using h

theorem assignment_product_split {s : ℕ} {I M : Type*} [CommMonoid M]
    (F : (Fin s → Fin s) → I → M)
    (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → I) :
    (∏ v : Fin s → Fin s, F v (a ((assignmentSplitEquiv s).symm v))) =
      (∏ e : Equiv.Perm (Fin s), F e (a (Sum.inl e))) *
        ∏ v : MissingAssignment s, F v.val (a (Sum.inr v)) := by
  classical
  calc
    _ = ∏ r : Equiv.Perm (Fin s) ⊕ MissingAssignment s,
        F (assignmentSplitEquiv s r) (a r) := by
      have h := (assignmentSplitEquiv s).prod_comp
        (fun v => F v (a ((assignmentSplitEquiv s).symm v)))
      simpa only [Equiv.symm_apply_apply] using h.symm
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

end Erdos3

end

end OAI
