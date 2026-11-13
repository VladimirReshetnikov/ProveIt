import Trace74Pell
import DiophantineConsistency.CompactFixedBeta

/-! Unchecked fixed-symbolic beta bound, without a graph-zero assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedQLarge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta Trace75Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

theorem fixed_q_large (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv0 : 0<v 0) :
    (1073741824:V)≤q p v := by
  have hj : 1≤v 0 := pos_iff_one_le.mp hv0
  have h30 : Exp.exp (30:V)=(1073741824:V) := by
    have hh := exp_nat_cast (V:=V) 30
    norm_num at hh
    exact hh
  have hb : (betaNat:V)+1=Exp.exp ((67:V)*8807) := CompactFixedBeta.beta_identity
  have hm : Exp.exp (30:V)≤Exp.exp ((67:V)*8807) := exp_monotone_le.mpr (by norm_num)
  rw [h30,←hb] at hm
  have hmul : (betaNat:V)≤(betaNat:V)*v 0 :=
    le_mul_of_one_le_right (by simp) hj
  calc
    (1073741824:V)≤(betaNat:V)+1 := hm
    _≤(betaNat:V)*v 0+1 := add_le_add_right hmul 1
    _=q p v := by simp only [q,b,hp0]; ring

#print axioms Trace74FixedQLarge.fixed_q_large
end Trace74FixedQLarge
