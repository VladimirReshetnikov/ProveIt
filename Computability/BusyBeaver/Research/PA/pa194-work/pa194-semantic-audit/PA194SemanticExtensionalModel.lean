import PA194SemanticNeighborhoodExact

/-! Extensionality as a named object-language assumption for the equality atom. -/
namespace PA194SemanticExtensionality
open M6.PA.NativeCalculus

def namedExtensionality : Named :=
  .all 0 (.all 1 (.imp (.all 2 (namedIff (.mem 2 0) (.mem 2 1))) (.eq 0 1)))

def incomingExtensionality {V : Type} (R : V → V → Prop) : Prop :=
  ∀ x y, (∀ t, R t x ↔ R t y) → x = y

theorem namedExtensionality_eval {V : Type} (R : V → V → Prop) (env : Nat → V) :
    namedExtensionality.eval R Eq env ↔ incomingExtensionality R := by
  classical
  simp [namedExtensionality,namedIff,namedAnd,Named.eval,incomingExtensionality,iff_def]

theorem observationalEq_iff_eq_of_extensional {V : Type} (R : V → V → Prop)
    (hext : incomingExtensionality R) (x y : V) : observationalEq R x y ↔ x = y := by
  constructor
  · intro h; exact hext x y h.2
  · intro h; subst y; exact ⟨fun _ => Iff.rfl,fun _ => Iff.rfl⟩

/-- The single equality-atom translation is sound in each extensional named
model when its reserved neighborhood binder is fresh. -/
theorem namedEquality_translation_of_extensionality {V : Type} (R : V → V → Prop)
    (env : Nat → V) (a b z : Nat) (ha : a ≠ z) (hb : b ≠ z)
    (hext : namedExtensionality.eval R Eq env) :
    (namedNeighborhood a b z).eval R Eq env ↔ (Named.eq a b).eval R Eq env := by
  apply (namedEquality_translation_iff R Eq env a b z ha hb).mpr
  exact observationalEq_iff_eq_of_extensional R ((namedExtensionality_eval R env).mp hext) (env a) (env b)

#print axioms namedExtensionality_eval
#print axioms observationalEq_iff_eq_of_extensional
#print axioms namedEquality_translation_of_extensionality
end PA194SemanticExtensionality
