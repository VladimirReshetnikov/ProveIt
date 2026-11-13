import Trace74Representatives

/-! UNCHECKED DRAFT: signed adjacent-Pell residue at the 74-induced
arbitrary difference-ring valuation; no positivity of synthetic alpha. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74Residue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellHalfIndex Trace75Factors Trace74Representatives
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_residue (p : Fin 4 → ℕ) (v : Fin 10 → V) (u : V)
    (hs : (regs (ports p) (masked p v)).V *
      (regs (ports p) (masked p v)).V = ι (u*u)) :
    SignMod (1+2*(delta p v*U p v*U p v*E p v)) u (c p v) := by
  let a : V := delta p v*U p v*U p v*E p v
  let F : V := 1+2*a
  let w : DiffRing V := (regs (ports p) (masked p v)).b
  have hF : 0<F := by dsimp [F]; simp
  have hx : (regs (ports p) (masked p v)).V=ι F*w-ι (c p v) := by
    rw [V_def,f_eq,a_eq,Trace74Representatives.delta_eval,Trace74Representatives.U_eval,
      Trace74Representatives.E_eval,Trace74Representatives.c_eval]
    dsimp [w,F,a]
    simp only [pow_two,map_mul,map_add,map_one,map_ofNat]
    ring
  exact Trace75Residue.multiple_residue F (c p v) u w _ hF hx hs

#print axioms Trace74Residue.graph_signed_residue
end Trace74Residue
