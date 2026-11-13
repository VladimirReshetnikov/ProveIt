import DiophantineConsistency.BFS943.Trace89Regs
import DiophantineConsistency.BFS943.Centred87Sign
import DiophantineConsistency.BFS943.Centred87Complete
import DiophantineConsistency.BFS943.Trace87ShiftSource
import DiophantineConsistency.BFS943.Trace87ModelIff

/-! # Both model directions of the 89/210 circuit at the BFS943 ports

Soundness: at a positive 89 zero, `Centred87Sign.shift_zero` (centre
`Trace89Centre.gnat`, bound `gnat_bound`) gives a shifted 87 zero
`Trace87ShiftTransport.ShiftZero p v (g₊ V)`, which is a
`BFS943FixedSource.FixedSource` at `Trace87Source.sourceVal`
(`Trace87ShiftSource.source_of_fixed_zero`); `FixedSourceHalt.source_halts`
gives a halting time of machine 215. Completeness: a halting time gives a
positive 87 zero (`Trace87HaltGraph.halt_zero_of_model_ports`), whose `V` is
positive (`Centred87Complete.V_positive`); moving `n` to `n + g₊ V`
(`Centred87Complete.centred_zero`) gives a positive 89 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace89ModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open CompactConstructedRank DirectBFSFourFieldsPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel rho
  DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem centred_value (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    TenPositiveTrace89.value89 (Trace87Factors.ports p) (fun j => ι (v j)) =
      TenPositiveCentred87.valueAt (Trace87Factors.ports p) (fun j => ι (v j))
        (ι (Trace89Centre.gnat p v)) := by
  rw [TenPositiveTrace89.value89,Trace89Centre.centre_eval]

theorem positive_model_iff (p : Fin 4 → ℕ)
    (hp0 : p 0 = betaNat) (hp1 : p 1 = DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2 = lowNat) (hp3 : p 3 = betaNat + highNat) :
    (∃ v : Fin 10 → V, (∀ j, 0 < v j) ∧
        TenPositiveTrace89.value89 (Trace87Factors.ports p) (fun j => ι (v j)) = 0) ↔
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
  have hb : 0 < (p 0 : V) := lt_of_lt_of_le (by norm_num) h31
  constructor
  · rintro ⟨v, hv, hz⟩
    rw [centred_value] at hz
    have hs := Centred87Sign.shift_zero p v (Trace89Centre.gnat p v) hb hv
      (Trace89Centre.gnat_bound p v hb hv) hz
    exact FixedSourceHalt.source_halts p (Trace87Source.sourceVal p v) hp0 hp1 hp2 hp3
      (Trace87Source.source_pos p v hb hv)
      (Trace87ShiftSource.source_of_fixed_zero p v hp0 hp2 hp3 hv hs)
  · rintro ⟨T, hT⟩
    obtain ⟨v, hv, hz⟩ := Trace87HaltGraph.halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m
    obtain ⟨V', _hV', hVeq⟩ := Centred87Complete.V_positive p v h31 hl hh hv hz
    obtain ⟨hv', hz'⟩ := Centred87Complete.centred_zero p v (Trace89Centre.gnat p v) V' hv hVeq hz
    refine ⟨Function.update v 7 (v 7 + Trace89Centre.gnat p v * V'), hv', ?_⟩
    rw [centred_value, Trace89Centre.gnat_update]
    exact hz'

#print axioms Trace89ModelIff.positive_model_iff
end Trace89ModelIff
