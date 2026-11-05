import IndependentYWitnessDraft

/-! Unchecked draft: all-model positive-zero join under two graph guards. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace IndependentYJoinDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_iff_of_guards (p : Fin 4 → ℕ)
    (hold : ∀v : Fin 14 → V, (∀i,0<v i) →
      InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output v →
      P64QCube76YBinding.oldV (fun j => (p j:ℤ)) (fun i => ι (v i)) + ι (v 12) ≠ 0)
    (hnew : ∀v : Fin 14 → V, (∀i,0<v i) →
      InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v →
      P64QCube76YBinding.oldV (fun j => (p j:ℤ)) (fun i => ι (v i)) < ι (v 12)) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output v) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · exact IndependentYWitnessDraft.new_to_old_conditional p v hv hz (hnew v hv hz)
  · exact IndependentYWitnessDraft.old_to_new_conditional p v hv hz (hold v hv hz)

#print axioms IndependentYJoinDraft.positive_zero_iff_of_guards
end IndependentYJoinDraft
