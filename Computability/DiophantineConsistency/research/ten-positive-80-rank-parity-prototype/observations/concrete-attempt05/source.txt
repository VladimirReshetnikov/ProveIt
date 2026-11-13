import Direct80FixedParity
import DiophantineConsistency.CompactSymbolicPorts

/-! Specialize the port bounds through explicit symbolic equalities. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80ConcreteParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticGcdNormalization CompactFixedBeta
open CompactSymbolicPorts TenPositive80Graph TenPositive80Factors
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port_equalities_even_and_unit (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    (∃w : V, q p v=2*w) ∧ Bez (b p v) (mu p v*mu p v) 1 := by
  have hb := CompactFixedBeta.bounds (1:V) (by simp)
  have hl : (p 2:V)<(p 0:V) := by
    rw [hp0,hp2]
    have he : (lowNat:V)=CompactConcreteIncrement.mask := by unfold lowNat CompactConcreteIncrement.mask; rfl
    rw [he]
    exact hb.2.1
  have hh : (p 3:V)<2*(p 0:V) := by
    rw [hp0,hp3,Nat.cast_add]
    have he : highNat=Nat.ofDigits (2^67) CompactHighPopulation.highDigits := by unfold highNat; rfl
    rw [he]
    exact hb.2.2.1
  exact Direct80FixedParity.graph_fixed_even_and_unit p v hp0 hl hh hv hz

#print axioms Direct80ConcreteParity.port_equalities_even_and_unit
end Direct80ConcreteParity
