import FreeMainSymbolicPortRankedMain
import FreeMainActualRankWindowCompact
import CompactSymbolicMaskData

/-! Source-only composition: the actual compact44 tuple, its rank window,
and the main Pell coordinates at that rank. No reverse map is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainFixedCompactRankedMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPellHalfIndex FreeMainConditionalRank
open FreeMainActualRankWindowCompact

attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask

/-- The opaque wrapper is exactly the symbolic fixed-port tuple used by the
    ranked-main theorem; this is a function equality, not a numerical evaluation. -/
private theorem compactPorts_eq (K : ℕ) : compactPorts K =
    CompactSymbolicPorts.ports CompactFixedBeta.betaNat K
      CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat := by
  unfold compactPorts
  rfl

attribute [local irreducible] compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- At the actual compact44 ports, an actual positive 72 zero has a positive
rank in the quartic window and its main Pell coordinates occur at that rank. -/
theorem fixed_main_at_rank (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    (0 < FreeMainActualRankWindowGeneric.rank p v ∧
      (ι (FreeMainActualRankWindowGeneric.rank p v):DiffRing V)+1 <
        (ι q)*(ι q*((ι q)*(ι q)))) ∧
    ∃ g : V, g*g=1+delta (aval p v)*(cval p v)*(cval p v) ∧
      xcoord (FreeMainAuxNorm.rank p v) (aval p v)=g ∧
      ycoord (FreeMainAuxNorm.rank p v) (aval p v)=cval p v := by
  have hwindow := compact_window K v hv hz
  have hz' : InternalZero (P64QCube72Free.graph
      (fun j => (CompactSymbolicPorts.ports CompactFixedBeta.betaNat K
        CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat j:ℤ))).output v := by
    rw [←compactPorts_eq K]
    exact hz
  have hb := CompactSymbolicMaskData.data (V:=V)
  have hmain := FreeMainSymbolicPortRankedMain.main_at_rank
    CompactFixedBeta.betaNat K CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat
    v hv hz' hb.2.2.2 hb.1 hb.2.1
  rw [←compactPorts_eq K] at hmain
  exact ⟨hwindow,hmain⟩

#print axioms fixed_main_at_rank
end FreeMainFixedCompactRankedMain
