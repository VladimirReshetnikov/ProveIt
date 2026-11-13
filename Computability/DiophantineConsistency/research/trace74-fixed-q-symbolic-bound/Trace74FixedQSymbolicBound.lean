import Trace74FixedQLarge

/-! The symbolic fixed beta supplies its full represented exponential bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedQSymbolicBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactFixedBeta Trace75Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- The first fixed port and a positive first witness force the full
represented exponential lower bound on the same tuple's `q`. -/
theorem fixed_q_symbolic_lower (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv0 : 0<v 0) :
    Exp.exp ((67:V)*8807)≤q p v := by
  have hj : 1≤v 0 := pos_iff_one_le.mp hv0
  have hb : (betaNat:V)+1=Exp.exp ((67:V)*8807) := CompactFixedBeta.beta_identity
  have hmul : (betaNat:V)≤(betaNat:V)*v 0 :=
    le_mul_of_one_le_right (by simp) hj
  calc
    Exp.exp ((67:V)*8807)=(betaNat:V)+1 := hb.symm
    _≤(betaNat:V)*v 0+1 := by simpa only [add_comm] using add_le_add_right hmul 1
    _=q p v := by simp only [q,b,hp0]

#print axioms Trace74FixedQSymbolicBound.fixed_q_symbolic_lower
end Trace74FixedQSymbolicBound
