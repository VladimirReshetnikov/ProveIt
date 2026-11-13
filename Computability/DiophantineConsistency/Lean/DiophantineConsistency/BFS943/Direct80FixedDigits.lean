import DiophantineConsistency.BFS943.Direct80FixedSaturation
import DiophantineConsistency.BFS943.Direct80NaturalTransport
import DiophantineConsistency.Compact44.CompactConcreteIncrement

/-! The compact low-mask digits and natural transport, sharing one graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80FixedDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticWindowDigits
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80SymbolicPortBounds TenPositive80NaturalTransport
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fixed_digits (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N t : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      0<Cnat p v ∧ ((p 1:V)+v 5)*Cnat p v=v 1+b p v*t ∧
      dig 67 (Cnat p v) 0=1 ∧ (∀ j<8807*N, dig 67 (Cnat p v) j≤3) ∧
      NoCarry (v 1) ((highNat:V)*v 0-1) := by
  obtain ⟨h31,hl,hh,hodd⟩ := fixed_bounds (V:=V) p hp0 hp2 hp3
  obtain ⟨N,hN,hJ,hq,_hpop,hnc,hnchigh⟩ :=
    Direct80FixedSaturation.graph_fixed_saturation p v hp0 hp2 hp3 hv hz
  obtain ⟨t,hC,ht⟩ := graph_natural_transport p v h31 hl hh hv hz hodd
  have hlow : (p 2:V)=CompactConcreteIncrement.mask := by
    rw [hp2]; unfold lowNat CompactConcreteIncrement.mask; rfl
  have hnc' : NoCarry (Cnat p v-1) (CompactConcreteIncrement.mask*rep (67*8807) N+1) := by
    simpa only [Cnat,hlow,hJ] using hnc
  obtain ⟨hzero,hdigits⟩ := CompactConcreteIncrement.recipe_digits N (Cnat p v) hN (pos_iff_one_le.mp hC) hnc'
  exact ⟨N,t,hN,hJ,hq,hC,ht,hzero,hdigits,hnchigh⟩

#print axioms Direct80FixedDigits.graph_fixed_digits
end Direct80FixedDigits
