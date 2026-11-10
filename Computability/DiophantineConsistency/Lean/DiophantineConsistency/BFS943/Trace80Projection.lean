import DiophantineConsistency.BFS943.Trace80Transport
import DiophantineConsistency.BFS943.Trace80NormRank
import DiophantineConsistency.BFS943.Trace75Projection
import DiophantineConsistency.BFS943.Direct80ProjectionProduct

/-! # Whole-product projection for the 80/258 circuit (chart q1)

At a positive zero of `value80`, `Trace80Transport.graph_zero_data` gives
`Z = M z` with `M = h q⁶ H`. Clearing the carrier gives `H ∣ q⁶ (h K)`; since
`H = q (4 s (X + 1)) - 1` is a unit modulo `q`, six cancellations give
`H ∣ h K`, hence the `Trace75Projection` divisibility `H ∣ (h X) K`.
`graph_entire_product` is then `Trace75GraphProduct.graph_entire_product`
with the q1 rank (`Trace80NormRank.graph_rank_exact`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace80Projection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace80
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open Trace80Factors Trace80NormRank

theorem cancel_pow {R : Type*} [CommRing R] (m t x : R) :
    ∀ n : ℕ, m*t-1∣m^n*x → m*t-1∣x
  | 0, h => by simpa using h
  | n+1, h => by
    apply cancel_pow m t x n
    apply Trace75Projection.cancel_base m t (m^n*x)
    have he : m^(n+1)*x=m*(m^n*x) := by ring
    rwa [he] at h

/-- The norm-layer hypotheses at a positive zero: the norm value at the
actual carrier, the mask and `q⁴ ∣ e`. -/
theorem zero_norm_data (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : value80 (ports p) (fun j => ι (v j)) = 0) :
    TenPositiveTrace76.normValue (regs (ports p) (fun j => ι (v j)))
        (regs (ports p) (fun j => ι (v j))).Z = 0 ∧
      v 1+v 2<q p v ∧
      (ι (q p v):DiffRing V)^4 ∣ (regs (ports p) (fun j => ι (v j))).e := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨_z,_tau,_f,_y,_,_,_,_,_,_,_,hm,hq4,_⟩ := Trace80Transport.graph_zero_data p v hb hv hz
  exact ⟨hz,hm,hq4⟩

theorem graph_projection_divisibility (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value80 (ports p) (fun j => ι (v j)) = 0) :
    let rr := regs (ports p) (fun j => ι (v j))
    rr.H∣(rr.h*rr.X)*rr.K := by
  let rr := regs (ports p) (fun j => ι (v j))
  obtain ⟨z,_tau,_f,_y,_,_,_,_,_,hZ,_,_,_,_⟩ := Trace80Transport.graph_zero_data p v hb hv hz
  have hM : rr.M=rr.h*rr.D*rr.H := M_def _ _
  rw [hM] at hZ
  have hshape : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-rr.b*rr.V*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*(rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6))) := Z_def _ _
  have hdiv : rr.H∣rr.D*(rr.h*rr.K) := by
    refine ⟨rr.h*rr.D*z-rr.h*rr.D*(ι (v 7)-rr.b*rr.V*rr.B)+rr.D*rr.B+
      rr.h*(rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)),?_⟩
    linear_combination -hshape+hZ
  have hH : rr.H=rr.q*(4*ι (v 6)*(rr.X+1))-1 := by
    change rr.H=_
    rw [H_def,Am1_def,Y_def]; ring
  have hD : rr.D*(rr.h*rr.K)=rr.q^6*(rr.h*rr.K) := by rw [D_def]; ring
  have hK : rr.H∣rr.h*rr.K := by
    rw [hH]
    apply cancel_pow rr.q (4*ι (v 6)*(rr.X+1)) (rr.h*rr.K) 6
    rw [←hH,←hD]
    exact hdiv
  change rr.H∣(rr.h*rr.X)*rr.K
  exact dvd_trans hK ⟨rr.X,by ring⟩

theorem graph_entire_product (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value80 (ports p) (fun j => ι (v j)) = 0) :
    let rr := regs (ports p) (fun j => ι (v j))
    rr.H∣(rr.h*rr.X)*(rr.X-ι (Exp.exp (rankNat p v)))*
      (ι (Exp.exp (rankNat p v))*rr.X+1) := by
  obtain ⟨hzn,hm,hq4⟩ := Trace80Projection.zero_norm_data p v hb31 hv hz
  let rr := regs (ports p) (fun j => ι (v j))
  let a : V := A p v-1
  let R : V := rankNat p v
  let C : V := c p v
  let d : V := xcoord R a
  let T : V := Exp.exp R
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos hq (hv 6)
  have hx : 0<X p v := mul_pos hq (mul_pos hq (hv 5))
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have ha1 : a+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hAeval : rr.Am1=ι (A p v) := by
    dsimp [rr,A,X,Y,q,b,ports]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast]
  have hCeval : rr.c=ι C := by
    dsimp [rr,C,c,k,X,Y,q,b,ports]
    simp only [c_def,k_def,Y_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast]
  have ha : (ι a:DiffRing V)+1=rr.Am1 := by
    rw [hAeval,←map_one (ι : V →+* DiffRing V),←map_add,ha1]
  have hH : rr.H=4*(ι a:DiffRing V)+3 := by
    rw [show rr.H=4*rr.Am1-1 by dsimp [rr]; rw [H_def]]
    rw [←ha]
    ring
  obtain ⟨_heval,_hlo,_hodd,hc,_hwindow⟩ := graph_rank_exact p v _ hb31 hl hh hv hzn hm
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
  have hdiv := graph_projection_divisibility p v hb hv hz
  change rr.H∣(rr.h*rr.X)*rr.K at hdiv
  rw [hH,hK] at hdiv
  have hdR' : (ι d:DiffRing V)=ι T+ι a*ι C+(4*ι a+3)*ι z := by
    exact hdR
  have hproduct := Direct80ProjectionProduct.entire_product (ι a:DiffRing V) (ι C) (ι d)
    (ι T) rr.X (rr.h*rr.X) (ι z) hdR' hnorm hdiv
  change rr.H∣(rr.h*rr.X)*(rr.X-ι T)*(ι T*rr.X+1)
  rwa [hH]

#print axioms Trace80Projection.graph_projection_divisibility
#print axioms Trace80Projection.graph_entire_product
end Trace80Projection
