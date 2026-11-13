import DiophantineConsistency.BFS943.Trace75GraphPower
import DiophantineConsistency.BFS943.Trace75RankExact
import DiophantineConsistency.BFS943.Direct80UnweightedProjection

/-! Weighted whole-product projection for the actual trace75 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75GraphUnweighted
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open Trace75Factors Trace75Rank Trace75RankExact
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_unweighted (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V))
    (hh : (p 3:V)<2*(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    let rr := regs (ports p) (fun j => ι (v j))
    rr.H∣rr.K := by
  let rr := regs (ports p) (fun j => ι (v j))
  let a : V := A p v-1
  let R : V := rankNat p v
  let C : V := c p v
  let d : V := xcoord R a
  let T : V := Exp.exp R
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
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
  obtain ⟨_heval,_hlo,_hodd,hc,_hwindow⟩ := graph_rank_exact p v hb31 hl hh hv hz
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
  have hXeval : rr.X=ι (X p v) := by
    dsimp [rr,X,q,b,ports]
    simp only [X_def,q_def,h_def,ports,map_mul,map_add,map_one,map_natCast]
  have hp := Trace75GraphPower.graph_power p v hb31 hl hh hv hz
  change X p v=T at hp
  have hTX : (ι T:DiffRing V)=rr.X := by rw [←hp,←hXeval]
  have hdR' : (ι d:DiffRing V)=rr.X+ι a*ι C+(4*ι a+3)*ι z := by
    rw [←hTX]
    exact hdR
  have hu := Direct80UnweightedProjection.unweighted (ι a:DiffRing V) (ι C) (ι d)
    rr.X (ι z) hdR' hnorm
  change rr.H∣rr.K
  rwa [hH,hK]

#print axioms Trace75GraphUnweighted.graph_unweighted
end Trace75GraphUnweighted
