import Trace75BFSHaltGraph
import Trace75BFSModelHalt
import CompactSymbolicBetaCast
import CompactSymbolicMaskData

/-! Join the two trace75 model directions at the same symbolic ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace75BFSModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open CompactConstructedRank DirectBFSFourFieldsPacking Trace75Factors
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel rho
  DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_model_iff (p : Fin 4 → ℕ)
    (hp0 : p 0 = betaNat) (hp1 : p 1 = DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2 = lowNat) (hp3 : p 3 = betaNat + highNat) :
    (∃ v : Fin 10 → V, (∀ j, 0 < v j) ∧ value75 (ports p) (fun j => ι (v j)) = 0) ↔
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
  constructor
  · rintro ⟨v, hv, hz⟩
    exact Trace75BFSModelHalt.graph_halts p v hp0 hp1 hp2 hp3 hv hz
  · rintro ⟨T, hT⟩
    exact Trace75BFSHaltGraph.halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m

#print axioms Trace75BFSModelIff.positive_model_iff
end Trace75BFSModelIff
