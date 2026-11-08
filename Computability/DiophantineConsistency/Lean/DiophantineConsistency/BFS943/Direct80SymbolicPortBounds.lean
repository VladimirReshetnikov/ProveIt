import DiophantineConsistency.BFS943.Direct80FixedBetaLower
import DiophantineConsistency.BFS943.Direct80FixedBetaOdd
import DiophantineConsistency.Compact44.CompactSymbolicPorts

/-! Symbolic port equalities imply the graph arithmetic side conditions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80SymbolicPortBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta CompactSymbolicPorts TenPositiveFixedBetaLower
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixed_bounds (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) :
    (31:V)≤(p 0:V) ∧ (p 2:V)<(p 0:V) ∧ (p 3:V)<2*(p 0:V) ∧
      ∃u : V, (p 0:V)=2*u+1 := by
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
  refine ⟨?_,hl,hh,?_⟩
  · rw [hp0]
    exact beta_ge_31
  · rw [hp0]
    exact Direct80FixedBetaOdd.beta_odd_model

#print axioms TenPositive80SymbolicPortBounds.fixed_bounds
end TenPositive80SymbolicPortBounds
