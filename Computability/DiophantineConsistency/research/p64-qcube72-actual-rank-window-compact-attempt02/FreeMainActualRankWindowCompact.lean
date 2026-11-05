import FreeMainActualRankWindowGeneric
import DiophantineConsistency.CompactSymbolicPorts

/-! Source-only specialization of the actual rank window to compact44 ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainActualRankWindowCompact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open FreeMainActualRankWindowGeneric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Specialize the two port inequalities to the compact44 symbolic masks. -/
theorem compact_window (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (CompactSymbolicPorts.ports CompactFixedBeta.betaNat K
        CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat j:ℤ))).output v) :
    let p := CompactSymbolicPorts.ports CompactFixedBeta.betaNat K
      CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat
    let q : V := (p 0:V)*v 0+1
    0<rank p v ∧ (ι (rank p v):DiffRing V)+1 < (ι q)*(ι q*((ι q)*(ι q))) := by
  let p := CompactSymbolicPorts.ports CompactFixedBeta.betaNat K
    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat
  have hb := CompactFixedBeta.bounds (V:=V) (v 0) (hv 0)
  have hMC : (p 2:V)<(p 0:V) := by
    change (CompactConcreteIncrement.mask : V) < (CompactFixedBeta.betaNat : V)
    exact hb.2.1
  have hMF : (p 3:V)<2*(p 0:V) := by
    change (((CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat : ℕ) : V)) <
      2*(CompactFixedBeta.betaNat : V)
    rw [Nat.cast_add]
    exact hb.2.2.1
  exact actual_window p v hv hz hMC hMF


#print axioms compact_window
end FreeMainActualRankWindowCompact
