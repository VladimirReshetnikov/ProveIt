import ModelEquivalence78To75
import ModelDiscrete75To74

/-! Source-only composition at natural ports. All component drafts and
transitive imports remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Model78To74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Natural-port positive-zero comparison through the 75 graph. -/
theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ) (hb : 0<(p 0 : V)) :
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P74PositiveGuard.graph (fun j => (p j : ℤ))).output v) := by
  have hfirst :
      (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
        InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v) ↔
      (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
        InternalZero (P75NegativePell.graph (fun j => (p j : ℤ))).output v) := by
    constructor
    · rintro ⟨v,hv,hz⟩
      exact ⟨v,hv,(ModelEquivalence7875Draft.zero_iff_natural_ports p v hb hv).mpr hz⟩
    · rintro ⟨v,hv,hz⟩
      exact ⟨v,hv,(ModelEquivalence7875Draft.zero_iff_natural_ports p v hb hv).mp hz⟩
  exact hfirst.trans (ModelDiscrete7574Draft.positive_zero_iff_natural_ports p hb)

end DiophantineConsistency.Model78To74Draft

#print axioms DiophantineConsistency.Model78To74Draft.positive_zero_iff_natural_ports
