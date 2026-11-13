import Trace74GraphProduct
import Trace74UniformProjectionReduction

/-! Draft. Reduced weighted projection for the same graph valuation and
arbitrary internal main Pell index at least two. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74UniformProjectionGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Representatives Trace74GraphProduct
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_reduced (p : Fin 4 → ℕ) (v : Fin 10 → V) (r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hr : (2:V)≤r) (hc : c p v=ycoord r (A p v-1)) :
    (4*ι (Y p v)*(ι (X p v)+1)-1 : DiffRing V) ∣
      ι (b p v)*(4*ι (Y p v)-1)*
        (4*(4*ι (Exp.exp (r-2))+1)*ι (Y p v)-1)*
        ((4*ι (Exp.exp (r-2))-1)*ι (Y p v)-ι (Exp.exp (r-2))) := by
  let rr := regs (ports p) (masked p v)
  have hrsub : r-2+2=r := tsub_add_cancel_of_le hr
  have hexp : Exp.exp r=4*Exp.exp (r-2) := by
    have hrsub' : (r-2+1)+1=r := by
      calc
        (r-2+1)+1=r-2+2 := by ring
        _=r := hrsub
    calc
      Exp.exp r=Exp.exp ((r-2+1)+1) := congrArg _ hrsub'.symm
      _=4*Exp.exp (r-2) := by rw [exp_succ,exp_succ]; ring
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
  have hp := graph_entire_product_odd p v r hb hv hz hc
  change rr.H∣(rr.h*rr.X)*(rr.X-ι (Exp.exp r))*(ι (Exp.exp r)*rr.X+1) at hp
  rw [hH,hh,hx,hexp] at hp
  simp only [map_mul,map_ofNat] at hp
  exact Trace74UniformProjectionReduction.reduce
    (ι (b p v)) (ι (X p v)) (ι (Y p v)) (ι (Exp.exp (r-2))) hp

#print axioms Trace74UniformProjectionGraph.graph_reduced
end Trace74UniformProjectionGraph
