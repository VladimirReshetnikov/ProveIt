import DiophantineConsistency.BFS943.FixedSourceHalt
import DiophantineConsistency.BFS943.Trace75Population
import DiophantineConsistency.BFS943.Trace75GraphPower
import DiophantineConsistency.BFS943.Trace75FixedBounds

/-! # A positive 75 zero is a `FixedSource`

Sanity check that `BFS943FixedSource.FixedSource` is the boundary the trace75
route actually crosses: at any ports with `31 ≤ β`, `MC < β`, `β + MF < 2β`
and `β + 1 = 2^d` (`d ≥ 2`), a positive zero of the 75/402 circuit gives the
four fields (`Trace75GraphPower.graph_power`,
`Trace75Transport.graph_transport_and_mask`,
`Trace75NaturalTransport.graph_natural_transport`,
`Trace75Population.graph_population`). At the direct-BFS943 ports the 75
halting theorem then factors through `FixedSourceHalt.source_halts`
(`trace75_halts_via_source`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FixedSourceOfTrace75
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel ArithmeticRepunit
open Trace75Factors Trace75Rank Trace75NaturalTransport BFS943FixedSource
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_of_zero (p : Fin 4 → ℕ) (v : Fin 10 → V) (d : V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hd : 2≤d) (hbeta : (p 0:V)+1=Exp.exp d) :
    FixedSource p v := by
  have hbpos : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  refine ⟨Trace75GraphPower.graph_power p v hb31 hl hh hv hz,
    (Trace75Transport.graph_transport_and_mask p v hbpos hv hz).2, ?_, ?_⟩
  · obtain ⟨t,_,ht⟩ := graph_natural_transport p v hb31 hl hh hv hz
    exact ⟨t,ht⟩
  · obtain ⟨N,_hN,hJ,hpop⟩ := Trace75Population.graph_population p v d hb31 hl hh hv hz hd hbeta
    have hpred : Exp.exp d-1=(p 0:V) := by rw [←hbeta]; simp
    have hq : q p v=Exp.exp (d*N) := by
      rw [←repunit_identity d N,hpred,←hJ]
      rfl
    exact ⟨d*N,hq,hpop⟩

/-- At the direct-BFS943 ports, a positive 75 zero is a `FixedSource`. -/
theorem source_of_fixed_zero (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    FixedSource p v := by
  obtain ⟨h31,hl,hh⟩ := Trace75FixedBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact beta_identity
  exact source_of_zero p v ((67:V)*8807) h31 hl hh hv hz (by norm_num) hb

/-- `Trace75BFSModelHalt.graph_halts`, factored through the source boundary. -/
theorem trace75_halts_via_source (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho) (hp2 : p 2=lowNat)
    (hp3 : p 3=betaNat+highNat) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t)=0 :=
  FixedSourceHalt.source_halts p v hp0 hp1 hp2 hp3 hv (source_of_fixed_zero p v hp0 hp2 hp3 hv hz)

#print axioms FixedSourceOfTrace75.source_of_zero
#print axioms FixedSourceOfTrace75.source_of_fixed_zero
#print axioms FixedSourceOfTrace75.trace75_halts_via_source
end FixedSourceOfTrace75
