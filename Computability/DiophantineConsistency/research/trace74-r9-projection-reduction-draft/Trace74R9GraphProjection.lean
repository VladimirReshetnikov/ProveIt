import Trace74GraphProduct
import Trace74R9ProjectionReduction

/-! UNCHECKED DRAFT. Same-tuple r=9 graph projection reduced to small factors. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74R9GraphProjection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Representatives Trace74GraphProduct Trace74R9ProjectionReduction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_r9_reduced (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hc : c p v=ycoord 9 (A p v-1)) :
    (4*ι (Y p v)*(ι (X p v)+1)-1 : DiffRing V) ∣
      ι (b p v)*(4*ι (Y p v)-1)*(2052*ι (Y p v)-1)*(511*ι (Y p v)-128) := by
  let rr := regs (ports p) (masked p v)
  have hexp : Exp.exp (9:V)=512 := by
    rw [show (9:V)=8+1 by ring,exp_succ,
      show (8:V)=7+1 by ring,exp_succ,
      show (7:V)=6+1 by ring,exp_succ,
      show (6:V)=5+1 by ring,exp_succ,
      show (5:V)=4+1 by ring,exp_succ,
      show (4:V)=3+1 by ring,exp_succ,
      show (3:V)=2+1 by ring,exp_succ,
      show (2:V)=1+1 by ring,exp_succ,
      show (1:V)=0+1 by ring,exp_succ,exp_zero]
    norm_num
  have hh : rr.h=ι (b p v) := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).h=ι (b p v)
    simp only [h_def,b,ports,map_mul,map_natCast]
  have hx : rr.X=ι (X p v) := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).X=ι (X p v)
    simp only [X_def,q_def,h_def,X,q,b,ports,map_mul,map_add,map_one,map_natCast]
  have hH : rr.H=4*ι (Y p v)*(ι (X p v)+1)-1 := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).H=4*ι (Y p v)*(ι (X p v)+1)-1
    simp only [H_def,Am1_def,X_def,Y_def,q_def,h_def,X,Y,q,b,ports,map_mul,map_add,map_one,map_natCast]
    ring
  have hp := graph_entire_product_odd p v (9:V) hb hv hz hc
  change rr.H∣(rr.h*rr.X)*(rr.X-ι (Exp.exp (9:V)))*(ι (Exp.exp (9:V))*rr.X+1) at hp
  rw [hH,hh,hx,hexp] at hp
  simp only [map_ofNat] at hp
  exact Trace74R9ProjectionReduction.reduce (ι (b p v)) (ι (X p v)) (ι (Y p v)) hp

#print axioms Trace74R9GraphProjection.graph_r9_reduced
end Trace74R9GraphProjection
