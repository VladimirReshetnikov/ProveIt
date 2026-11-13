import DiophantineConsistency.Sign14Positive74ObjectCoordinateArrangement

/-! SOURCE-ONLY: syntactic focusing and its open substitution action. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCoordinateFocus
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage Sign14Positive74ObjectCoordinateArrangement

def focusFormula {n : ℕ} (i : Fin (n+1)) (φ : Semisentenceᵢ language (n+1)) :
    Semisentenceᵢ language (n+1) :=
  Rew.subst (fun j => #(focusIndex i j)) ▹ φ

theorem focus_subst {n : ℕ} (i : Fin (n+1)) (φ : Semisentenceᵢ language (n+1))
    (x : Term language ℕ) (v : Fin (n+1) → Term language ℕ) :
    Rew.embSubsts (Fin.cons x (i.removeNth v)) ▹ focusFormula i φ =
      Rew.embSubsts (Function.update v i x) ▹ φ := by
  have hrew : (Rew.embSubsts (Fin.cons x (i.removeNth v))).comp
      (Rew.subst (fun j => #(focusIndex i j))) =
      Rew.embSubsts (Function.update v i x) := by
    ext j
    · simpa [Rew.comp_app] using congrFun (focus_assignment i x v) j
    · exact Empty.elim j
  simpa only [focusFormula, ← TransitiveRewriting.comp_app, hrew]
end DiophantineConsistency.Sign14Positive74ObjectCoordinateFocus
#print axioms DiophantineConsistency.Sign14Positive74ObjectCoordinateFocus.focus_subst
