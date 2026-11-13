import FreeMainActualRankWindowGeneric
import CompactSymbolicMaskData
import CompactGenericPortProjections

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
def compactPorts (K : ℕ) : Fin 4 → ℕ :=
  CompactSymbolicPorts.ports CompactFixedBeta.betaNat K
    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat

attribute [local irreducible] CompactFixedBeta.betaNat
  CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat Nat.ofDigits
  CompactListMask.digits CompactConcreteMask.support CompactHighPopulation.highDigits
  CompactConcreteIncrement.mask

theorem compactPorts_zero (K : ℕ) : compactPorts K 0 = CompactFixedBeta.betaNat := by
  unfold compactPorts
  exact CompactGenericPortProjections.at_zero _ _ _ _

theorem compactPorts_two (K : ℕ) : compactPorts K 2 = CompactSymbolicPorts.lowNat := by
  unfold compactPorts
  exact CompactGenericPortProjections.at_two _ _ _ _

theorem compactPorts_three (K : ℕ) : compactPorts K 3 =
    CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat := by
  unfold compactPorts
  exact CompactGenericPortProjections.at_three _ _ _ _

attribute [local irreducible] compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Specialize the two port inequalities to the compact44 symbolic masks. -/
theorem compact_window (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    0<rank p v ∧ (ι (rank p v):DiffRing V)+1 < (ι q)*(ι q*((ι q)*(ι q))) := by
  let p := compactPorts K
  have hb := CompactSymbolicMaskData.data (V:=V)
  have hMC : (p 2:V)<(p 0:V) := by
    dsimp only [p]
    rw [compactPorts_two,compactPorts_zero]
    exact hb.1
  have hMF : (p 3:V)<2*(p 0:V) := by
    dsimp only [p]
    rw [compactPorts_three,compactPorts_zero,Nat.cast_add]
    exact hb.2.1
  exact actual_window p v hv hz hMC hMF


#print axioms compact_window
end FreeMainActualRankWindowCompact
