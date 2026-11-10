import DiophantineConsistency.BFS943.Trace111Regs
import DiophantineConsistency.BFS943.Scaled87Sign
import DiophantineConsistency.BFS943.Scaled87Complete
import DiophantineConsistency.BFS943.Centred87Complete
import DiophantineConsistency.BFS943.Trace87ShiftSource
import DiophantineConsistency.BFS943.Trace87ModelIff

/-! # Both model directions of the 111/198 `product2` circuit at the BFS943 ports

Soundness: the circuit is the root-scale-two norm at `Z₈₇ - M Ω₂`
(`TenPositiveTrace111.value111_eq`); `Scaled87Sign.shift_zero` with the size bound
`Trace111Omega.omega_shift` (`Ω₂ ≤ 3 A U E |V| < 5 g |V|`, no sign of `b`, `V`) gives a shifted 87 zero
`Trace87ShiftTransport.ShiftZero`, which is a `BFS943FixedSource.FixedSource`
at `Trace87Source.sourceVal` (`Trace87ShiftSource.source_of_fixed_zero`);
`FixedSourceHalt.source_halts` gives a halting time of machine 215.
Completeness: a halting time gives a positive 87 zero
(`Trace87HaltGraph.halt_zero_of_model_ports`) with `V > 0`
(`Centred87Complete.V_positive`); then `Ω₂ ≥ 0` (`Trace111Omega.omega_nonneg`), and
`Scaled87Complete.scaled_zero` at the natural shift `Ω₂` moves `n` to a
positive zero of the 111 circuit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Trace111ModelIff
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
        TenPositiveTrace111.value111 (Trace87Factors.ports p) (fun j => ι (v j)) = 0) ↔
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
    rw [TenPositiveTrace111.value111_eq] at hz
    obtain ⟨w', hs⟩ := Scaled87Sign.shift_zero p v _ hb hv (Trace111Omega.omega_shift p v hb hv) hz
    exact FixedSourceHalt.source_halts p (Trace87Source.sourceVal p v) hp0 hp1 hp2 hp3
      (Trace87Source.source_pos p v hb hv)
      (Trace87ShiftSource.source_of_fixed_zero p v hp0 hp2 hp3 hv hs)
  · rintro ⟨T, hT⟩
    obtain ⟨v, hv, hz⟩ := Trace87HaltGraph.halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m
    obtain ⟨V', hV'pos, hVeq⟩ := Centred87Complete.V_positive p v h31 hl hh hv hz
    have hVpos : 0 < (TenPositiveTrace87.regs (Trace87Factors.ports p) (fun j => ι (v j))).V := by
      rw [hVeq, ← map_zero (ι : V →+* DiffRing V), ι_lt_ι]
      exact hV'pos
    obtain ⟨C', hC'⟩ := nonneg_iff.mp (Trace111Omega.omega_nonneg p v hb hv hVpos)
    obtain ⟨n', hn', hzero⟩ := Scaled87Complete.scaled_zero p v C' hb hv hz
    refine ⟨Function.update v 7 n', ?_, ?_⟩
    · intro j
      by_cases h : j = 7
      · subst h
        rw [Function.update_self]
        exact hn'
      · rw [Function.update_of_ne h]
        exact hv j
    · rw [Scaled87Complete.cast_update v n', TenPositiveTrace111.value111_update, hC',
        ← Scaled87Complete.cast_update v n']
      exact hzero

#print axioms Trace111ModelIff.positive_model_iff
end Trace111ModelIff
