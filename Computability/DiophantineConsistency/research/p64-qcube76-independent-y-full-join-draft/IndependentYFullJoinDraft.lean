import IndependentYJoinDraft
import IndependentYOldRootDraft
import IndependentYStrictDraft

/-! Unchecked draft: discharge both conditional 76Y/77 witness guards. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace IndependentYFullJoinDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_iff (p : Fin 4 → ℕ) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output v) :=
  IndependentYJoinDraft.positive_zero_iff_of_guards p
    (fun v hv hz => IndependentYOldRootDraft.old_root_ne_zero p v hv hz)
    (fun v hv hz => IndependentYStrictDraft.actual_strict p v hv hz)

#print axioms IndependentYFullJoinDraft.positive_zero_iff
end IndependentYFullJoinDraft
