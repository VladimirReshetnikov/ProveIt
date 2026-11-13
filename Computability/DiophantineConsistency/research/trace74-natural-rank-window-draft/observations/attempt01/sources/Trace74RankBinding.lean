import Trace74NaturalRankWindow
import Trace74Representatives

/-! UNCHECKED DRAFT. The 74-induced signed graph rank has the scalar natural
representative when F<q and C≤q; the reverse sum guard is not used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74RankBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74Representatives Trace74NaturalRankWindow

section Ring
variable {R : Type*} [CommRing R]
theorem ring_rank_shape (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p (Trace74Mask.oldVal p v)).rank =
      ((p 0*v 0+1)*((p 0*v 0+1)-v 1)-v 2)*((p 0*v 0+1)^2-1)+
        (p 2+(p 0*v 0+1)*p 3)*v 0 := by
  change (p 0*v 0*((p 0*v 0+1)-v 1)+((p 0*v 0+1)-v 1-v 2))*
    ((p 0*v 0+1)*(p 0*v 0+1)-1)+(p 2+(p 0*v 0+1)*p 3)*v 0 = _
  ring
end Ring

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem cast_tsub (a b : V) (h : b≤a) :
    ι (a-b) = (ι a : DiffRing V)-ι b := by
  apply eq_sub_iff_add_eq.mpr
  rw [←map_add,tsub_add_cancel_of_le h]

theorem graph_rank_eval (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hF : v 1<q p v) (hC : v 2≤q p v) :
    (regs (ports p) (masked p v)).rank =
      ι (rank (q p v) (p 2:V) (p 3:V) (v 0) (v 1) (v 2)) := by
  have hqpos : 0<q p v := by dsimp [q,b]; simp
  have hqF : v 1≤q p v := le_of_lt hF
  have hv : 0<q p v-v 1 := tsub_pos_iff_lt.mpr hF
  have hCmul : v 2≤q p v*(q p v-v 1) := le_trans hC
    (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hv))
  have hq2 : 1≤(q p v)^2 := by
    simpa only [pow_two] using one_le_mul (pos_iff_one_le.mp hqpos) (pos_iff_one_le.mp hqpos)
  change (regs (ports p) (Trace74Mask.oldVal (ports p) (fun j => ι (v j)))).rank = _
  rw [ring_rank_shape]
  simp only [rank,map_add,map_mul,map_pow,map_one,map_natCast,
    cast_tsub (q p v) (v 1) hqF,
    cast_tsub (q p v*(q p v-v 1)) (v 2) hCmul,
    cast_tsub ((q p v)^2) 1 hq2]
  simp only [ports,q,b,map_add,map_mul,map_one,map_natCast]
  ring

#print axioms Trace74RankBinding.ring_rank_shape
#print axioms Trace74RankBinding.graph_rank_eval
end Trace74RankBinding
