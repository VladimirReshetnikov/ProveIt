import Compact78To85
import ModelEquivalence85To86

/-! Source-only symbolic compact-port 78↔86 composition. All imported
model/graph clients remain unelaborated; no endpoint or file theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Compact78To86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed all-positive 78↔86 comparison at symbolic compact ports,
with arbitrary natural K and beta+highNat in the fourth slot. -/
theorem positive_zero_iff (K : ℕ) :
    let p : Fin 4 → ℕ := ports CompactFixedBeta.betaNat K lowNat highNat
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v) ↔
    (∃ v : Fin 14 → V, (∀ j, 0<v j) ∧
      InternalZero (P86ResidueGraph.graph (fun j => (p j : ℤ))).output v) := by
  let p : Fin 4 → ℕ := ports CompactFixedBeta.betaNat K lowNat highNat
  have hb := C44Short15Facts.port_bounds (V:=V) CompactFixedBeta.betaNat K lowNat highNat
    CompactFixedBeta.beta_identity rfl rfl
  exact (Compact78To85Draft.positive_zero_iff K).trans
    (ModelEquivalence8586Draft.positive_zero_iff_natural_ports p hb.1)

end DiophantineConsistency.Compact78To86Draft

#print axioms DiophantineConsistency.Compact78To86Draft.positive_zero_iff
