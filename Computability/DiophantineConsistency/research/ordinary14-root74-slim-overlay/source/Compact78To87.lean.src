import Compact78To86
import CompactEquivalence8687

/-! Source-only compact symbolic 78↔87 composition. All graph/model
imports remain unelaborated; no endpoint or file result is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Compact78To87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed positive 78↔87 comparison at symbolic compact ports with
arbitrary natural K and beta+highNat in the fourth slot. -/
theorem positive_zero_iff (K : ℕ) :
    let p : Fin 4 → ℕ := ports CompactFixedBeta.betaNat K lowNat highNat
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P87ShiftedGuard.graph (fun j => (p j : ℤ))).output v) := by
  exact (Compact78To86Draft.positive_zero_iff K).trans
    (CompactEquivalence8687Draft.positive_zero_iff K)

end DiophantineConsistency.Compact78To87Draft

#print axioms DiophantineConsistency.Compact78To87Draft.positive_zero_iff
