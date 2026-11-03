import DiophantineConsistency.CompactFixedBeta
import DiophantineConsistency.CompactSymbolicPorts

/-! Symbolic fixed-port inequalities, with no graph-specific import. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75FixedBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta CompactSymbolicPorts
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem beta_ge_31 : (31:V)≤(betaNat:V) := by
  have hsmall : Exp.exp (5:V)=32 := by
    rw [show (5:V)=4+1 by ring,exp_succ,show (4:V)=3+1 by ring,exp_succ,
      show (3:V)=2+1 by ring,exp_succ,show (2:V)=1+1 by ring,exp_succ,
      show (1:V)=0+1 by ring,exp_succ]
    norm_num
  have hindex : (5:V)≤(67:V)*8807 := by norm_num
  have hexp : (32:V)≤Exp.exp ((67:V)*8807) := by
    rw [←hsmall]
    exact exp_monotone_le.mpr hindex
  rw [←CompactFixedBeta.beta_identity] at hexp
  apply (add_le_add_iff_right (1:V)).mp
  simpa only [show (31:V)+1=32 by ring] using hexp

theorem fixed_bounds (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) :
    (31:V)≤(p 0:V) ∧ (p 2:V)<(p 0:V) ∧ (p 3:V)<2*(p 0:V) := by
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
  refine ⟨?_,hl,hh⟩
  rw [hp0]
  exact beta_ge_31

#print axioms Trace75FixedBounds.beta_ge_31
#print axioms Trace75FixedBounds.fixed_bounds
end Trace75FixedBounds
