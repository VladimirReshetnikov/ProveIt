import DiophantineConsistency.BFS943.Trace87Source
import DiophantineConsistency.BFS943.Trace87HaltGraph
import DiophantineConsistency.BFS943.FixedSourceHalt
import DiophantineConsistency.BFS943.Trace75FixedBounds
import DiophantineConsistency.Compact44.CompactSymbolicBetaCast
import DiophantineConsistency.Compact44.CompactSymbolicMaskData

/-! # Both model directions of the 87/214 circuit at the BFS943 ports

Soundness: a positive 87 zero is a `BFS943FixedSource.FixedSource` at the
source coordinates `Trace87Source.sourceVal` (`Trace87Source.source_of_fixed_zero`),
and `FixedSourceHalt.source_halts` gives a halting time of machine 215. No 75
or 82 zero is constructed. Completeness: a halting time gives a positive 87 zero
directly (`Trace87HaltGraph.halt_zero_of_model_ports`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace87ModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open CompactConstructedRank DirectBFSFourFieldsPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel rho
  DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_model_iff (p : Fin 4 → ℕ)
    (hp0 : p 0 = betaNat) (hp1 : p 1 = DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2 = lowNat) (hp3 : p 3 = betaNat + highNat) :
    (∃ v : Fin 10 → V, (∀ j, 0 < v j) ∧
        TenPositiveTrace87.value87 (Trace87Factors.ports p) (fun j => ι (v j)) = 0) ↔
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
  obtain ⟨h31, _hl, _hh⟩ := Trace75FixedBounds.fixed_bounds (V := V) p hp0 hp2 hp3
  have hb : 0 < (p 0 : V) := lt_of_lt_of_le (by norm_num) h31
  constructor
  · rintro ⟨v, hv, hz⟩
    exact FixedSourceHalt.source_halts p (Trace87Source.sourceVal p v) hp0 hp1 hp2 hp3
      (Trace87Source.source_pos p v hb hv)
      (Trace87Source.source_of_fixed_zero p v hp0 hp2 hp3 hv hz)
  · rintro ⟨T, hT⟩
    exact Trace87HaltGraph.halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m

#print axioms Trace87ModelIff.positive_model_iff
end Trace87ModelIff
