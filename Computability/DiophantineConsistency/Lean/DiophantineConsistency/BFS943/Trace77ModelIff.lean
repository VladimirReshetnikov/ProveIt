import DiophantineConsistency.BFS943.Trace77ToTrace75
import DiophantineConsistency.BFS943.Trace77FromTrace76
import DiophantineConsistency.BFS943.Trace76HaltGraph
import DiophantineConsistency.BFS943.Trace75BFSModelHalt
import DiophantineConsistency.BFS943.Trace75FixedBounds
import DiophantineConsistency.Compact44.CompactSymbolicBetaCast
import DiophantineConsistency.Compact44.CompactSymbolicMaskData

/-! # Both model directions of the 77/348 circuit at the BFS943 ports

Soundness: a positive 77 zero gives a positive 75 zero
(`Trace77ToTrace75.positive75_of_positive77`), and the 75 chain
`Trace75BFSModelHalt.graph_halts` gives a halting time of machine 215.
Completeness: halting gives a positive 76 zero
(`Trace76HaltGraph.halt_zero_of_model_ports`), which gives a positive 77
zero (`Trace77FromTrace76.positive77_of_positive76`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace77ModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 TenPositiveTrace77
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open CompactConstructedRank DirectBFSFourFieldsPacking Trace75Factors
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel rho
  DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_model_iff (p : Fin 4 → ℕ)
    (hp0 : p 0 = betaNat) (hp1 : p 1 = DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2 = lowNat) (hp3 : p 3 = betaNat + highNat) :
    (∃ v : Fin 10 → V, (∀ j, 0 < v j) ∧ value77 (ports p) (fun j => ι (v j)) = 0) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  have hp0m : (p 0 : V) = Exp.exp (590069 : V) - 1 := by
    rw [hp0]
    exact CompactSymbolicBetaCast.beta_model
  have hp1m : (p 1 : V) = (kernel : V) := by
    unfold DirectBFSFourFieldsPacking.kernel
    exact congrArg (fun k : ℕ => (k : V)) hp1
  have hp2m : (p 2 : V) = low := by
    rw [hp2]
    exact CompactSymbolicMaskData.low_eq
  have hp3m : (p 3 : V) = high + (Exp.exp (590069 : V) - 1) := by
    rw [hp3, Nat.cast_add, CompactSymbolicBetaCast.beta_model]
    have hh : (highNat : V) = high := CompactSymbolicMaskData.high_eq
    rw [hh, add_comm]
  obtain ⟨h31, hl, hh⟩ := Trace75FixedBounds.fixed_bounds (V := V) p hp0 hp2 hp3
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨w, hw, hz75⟩ := Trace77ToTrace75.positive75_of_positive77 p v h31 hl hh hv hz
    exact Trace75BFSModelHalt.graph_halts p w hp0 hp1 hp2 hp3 hw hz75
  · rintro ⟨T, hT⟩
    obtain ⟨v, hv, hz76⟩ := Trace76HaltGraph.halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m
    exact Trace77FromTrace76.positive77_of_positive76 p v h31 hl hh hv hz76

#print axioms Trace77ModelIff.positive_model_iff
end Trace77ModelIff
