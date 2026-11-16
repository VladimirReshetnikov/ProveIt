import PA194SemanticExtensionality

/-! Exact standard named semantics of the PA194 neighborhood equality formula,
under explicit freshness of the bound label. No total numeric decoder is assumed. -/
namespace PA194SemanticExtensionality
open M6.PA.NativeCalculus

def observationalEq {V : Type} (R : V → V → Prop) (x y : V) : Prop :=
  (∀ t, R x t ↔ R y t) ∧ (∀ t, R t x ↔ R t y)

theorem namedNeighborhood_eval {V : Type} (R E : V → V → Prop) (env : Nat → V)
    (a b z : Nat) (ha : a ≠ z) (hb : b ≠ z) :
    (namedNeighborhood a b z).eval R E env ↔ observationalEq R (env a) (env b) := by
  classical
  simp [namedNeighborhood,namedAnd,namedIff,Named.eval,observationalEq,ha,hb,iff_def]

/-- This is the exact equality obligation for this named neighborhood reading. -/
theorem namedEquality_translation_iff {V : Type} (R E : V → V → Prop) (env : Nat → V)
    (a b z : Nat) (ha : a ≠ z) (hb : b ≠ z) :
    ((namedNeighborhood a b z).eval R E env ↔ (Named.eq a b).eval R E env) ↔
      (observationalEq R (env a) (env b) ↔ E (env a) (env b)) := by
  rw [namedNeighborhood_eval R E env a b z ha hb]
  rfl

#print axioms namedNeighborhood_eval
#print axioms namedEquality_translation_iff
end PA194SemanticExtensionality
