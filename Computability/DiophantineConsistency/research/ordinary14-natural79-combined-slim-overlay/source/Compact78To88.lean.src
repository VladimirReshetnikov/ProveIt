import Compact78To87
import CompactEquivalence8788

/-! Source-only compact symbolic 78↔88 composition. All graph/model
imports remain unelaborated; no endpoint or file result is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Compact78To88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive 78↔88 comparison at symbolic compact ports with
arbitrary natural K and beta+highNat in the fourth slot. -/
theorem positive_zero_iff (K : ℕ) :
    let p : Fin 4 → ℕ := ports CompactFixedBeta.betaNat K lowNat highNat
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P88QuotientGuarded.graph (fun j => (p j : ℤ))).output v) := by
  exact (Compact78To87Draft.positive_zero_iff K).trans
    (CompactEquivalence8788Draft.positive_zero_iff K)

end DiophantineConsistency.Compact78To88Draft

#print axioms DiophantineConsistency.Compact78To88Draft.positive_zero_iff
