import DiophantineConsistency.CompactFixedBeta

/-! Unchecked model bound for the fixed symbolic beta. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedBeta31
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

theorem beta_ge_31 : (31:V)≤(betaNat:V) := by
  have he : Exp.exp (5:V)=(32:V) := by
    have hh := exp_nat_cast (V:=V) 5
    norm_num at hh
    exact hh
  have hb : (betaNat:V)+1=Exp.exp ((67:V)*8807) := CompactFixedBeta.beta_identity
  have hm : Exp.exp (5:V)≤Exp.exp ((67:V)*8807) := exp_monotone_le.mpr (by norm_num)
  rw [he,←hb] at hm
  apply (add_le_add_iff_right (1:V)).mp
  simpa only [show (31:V)+1=32 by norm_num] using hm

#print axioms Trace74FixedBeta31.beta_ge_31
end Trace74FixedBeta31
