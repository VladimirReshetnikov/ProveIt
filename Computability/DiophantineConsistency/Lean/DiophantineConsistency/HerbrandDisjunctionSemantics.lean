import Foundation.FirstOrder.Basic.Semantics.Semantics
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandDisjunctionSemantics
open LO LO.FirstOrder
open scoped LO.FirstOrder
/-- A recursively formed finite disjunction holds exactly when one of its
listed disjuncts holds. -/
theorem eval_list_disjunction {L : Language} {M : Type} [Structure L M] {α : Type}
    (item : α → Proposition L) (out : List α → Proposition L)
    (hnil : out [] = ⊥) (hcons : ∀ a as, out (a :: as) = item a ⋎ out as)
    (xs : List α) (e : ℕ → M) :
    (out xs).Eval ![] e ↔ ∃ a ∈ xs, (item a).Eval ![] e := by
  induction xs with
  | nil => rw [hnil]; simp [Semiformula.Eval]
  | cons a as ih =>
    rw [hcons]
    change ((item a).Eval ![] e ∨ (out as).Eval ![] e) ↔ _
    rw [ih]
    simp
end DiophantineConsistency.HerbrandDisjunctionSemantics
