import Foundation.FirstOrder.Arithmetic.Schemata
/-! Syntax for the side-disjunction used in the Σ₁ induction-rule reduction. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

/-- E may contain arbitrary free parameters, but no induction bound variable. -/
def guard {L : Language} (φ : Semiproposition L 1) (E : Proposition L) :
    Semiproposition L 1 := φ ⋎ (Rew.bShift ▹ E)

/-- The side formula is unchanged for every term, even one with parameters. -/
@[simp] theorem guard_subst {L : Language} (φ : Semiproposition L 1)
    (E : Proposition L) (t : SyntacticTerm L) :
    (guard φ E)/[t] = φ/[t] ⋎ E := by
  simp [guard, ← TransitiveRewriting.comp_app]

/-- The guarded formula is admissible to a Σ₁ induction rule. -/
theorem guard_sigma {L : Language} [L.LT] (φ : Semiproposition L 1) (E : Proposition L)
    (hφ : Hierarchy 𝚺 1 φ) (hE : Hierarchy 𝚺 1 E) :
    Hierarchy 𝚺 1 (guard φ E) := by
  simp only [guard, Hierarchy.or_iff]; exact ⟨hφ, by simpa using hE⟩

end DiophantineConsistency.ParsonsGuard
