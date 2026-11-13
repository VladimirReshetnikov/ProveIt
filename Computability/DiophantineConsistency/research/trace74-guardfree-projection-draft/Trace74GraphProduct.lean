import Trace74Projection
import Trace74Fold
import Direct80ProjectionProduct

/-! UNCHECKED DRAFT. Guard-free weighted projection for an actual trace74 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74GraphProduct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open Trace75Factors Trace74Representatives Trace74Projection Trace74Fold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_entire_product_odd (p : Fin 4 → ℕ) (v : Fin 10 → V) (r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hc : c p v=ycoord r (A p v-1)) :
    let rr := regs (ports p) (masked p v)
    rr.H∣(rr.h*rr.X)*(rr.X-ι (Exp.exp r))*(ι (Exp.exp r)*rr.X+1) := by
  let rr := regs (ports p) (masked p v)
  let a : V := A p v-1
  let R : V := r
  let C : V := c p v
  let d : V := xcoord R a
  let T : V := Exp.exp R
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have ha1 : a+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hAeval : rr.Am1=ι (A p v) := by
    dsimp [rr]
    change (regs (ports p) (fun j => ι (v j))).Am1=ι (A p v)
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hCeval : rr.c=ι C := by
    exact Trace74Representatives.c_eval p v
  have ha : (ι a:DiffRing V)+1=rr.Am1 := by
    rw [hAeval,←map_one (ι : V →+* DiffRing V),←map_add,ha1]
  have hH : rr.H=4*(ι a:DiffRing V)+3 := by
    rw [show rr.H=4*rr.Am1-1 by dsimp [rr]; rw [H_def]]
    rw [←ha]
    ring
  change C=ycoord R a at hc
  obtain ⟨z,hd⟩ := projection_quotient a R
  change d=T+a*ycoord R a+(4*a+3)*z at hd
  rw [←hc] at hd
  have hn : d*d=1+ArithmeticPellRecurrence.delta a*C*C := by
    dsimp [d]
    rw [hc]
    exact norm R a
  have hdR := congrArg (fun x : V => (ι x:DiffRing V)) hd
  have hnR := congrArg (fun x : V => (ι x:DiffRing V)) hn
  simp only [map_add,map_mul,map_one,map_ofNat] at hdR hnR
  have hnorm : (ι d:DiffRing V)*ι d=1+
      ((ι a:DiffRing V)*ι a+(4*ι a+3))*ι C*ι C := by
    have hdelta : (ι (ArithmeticPellRecurrence.delta a):DiffRing V)=
        (ι a:DiffRing V)*ι a+(4*ι a+3) := by
      simp only [ArithmeticPellRecurrence.delta,map_mul,map_add,map_one,map_ofNat]
      ring
    rw [hdelta] at hnR
    exact hnR
  have hK : rr.K=(4*(ι a:DiffRing V)+3)*rr.X*ι C-
      2*(rr.X*rr.X+2*ι a*rr.X*ι C-1) := by
    rw [show rr.K=rr.X*(3*rr.c-2*rr.X)+2 by dsimp [rr]; rw [K_def],hCeval]
    ring
  have hdiv := Trace74Projection.graph_projection_divisibility p v hb hv hz
  change rr.H∣(rr.h*rr.X)*rr.K at hdiv
  rw [hH,hK] at hdiv
  have hdR' : (ι d:DiffRing V)=ι T+ι a*ι C+(4*ι a+3)*ι z := by
    exact hdR
  have hproduct := Direct80ProjectionProduct.entire_product (ι a:DiffRing V) (ι C) (ι d)
    (ι T) rr.X (rr.h*rr.X) (ι z) hdR' hnorm hdiv
  change rr.H∣(rr.h*rr.X)*(rr.X-ι T)*(ι T*rr.X+1)
  rwa [hH]

theorem graph_odd_projection (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ r : V, 0<r ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) ∧
      let rr := regs (ports p) (masked p v)
      rr.H∣(rr.h*rr.X)*(rr.X-ι (Exp.exp r))*(ι (Exp.exp r)*rr.X+1) := by
  obtain ⟨r,j,I,hr,hrj,hodd,hj,hI,hc,hx,hy,hdiv⟩ := graph_odd_ordinate p v hb hv hz
  exact ⟨r,hr,hodd,hc,graph_entire_product_odd p v r hb hv hz hc⟩

#print axioms Trace74GraphProduct.graph_entire_product_odd
#print axioms Trace74GraphProduct.graph_odd_projection
end Trace74GraphProduct
