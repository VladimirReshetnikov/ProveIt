import ModelMapParentTo88
import ModelMap88ToParent
import DiophantineConsistency.Compact44.P72Root

/-! Source-only positive model comparison at natural ports. Both witness
maps and all their imports remain unelaborated; no endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Parent88EquivalenceDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive-zero equivalence at arbitrary natural ports with
positive beta. No K upper bound or mask inequality is assumed. -/
theorem positive_zero_iff (p : Fin 4 → ℕ) (hb : 0<(p 0:V)) :
    (∃ v : Fin 13 → V, (∀ j, 0<v j) ∧
      InternalZero (P88FourSquare.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ w : Fin 14 → V, (∀ j, 0<w j) ∧
      InternalZero (P88QuotientGuarded.graph (fun j => (p j : ℤ))).output w) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact ModelMapParentTo88Draft.positive_map p v hb hv hz
  · rintro ⟨w,hw,hz⟩
    exact ModelMap88ToParentDraft.positive_map (fun j => (p j : ℤ)) (p 0:V) w hb
      (P72Root.cast_port p 0) hw hz

end DiophantineConsistency.Parent88EquivalenceDraft

#print axioms DiophantineConsistency.Parent88EquivalenceDraft.positive_zero_iff
