import Direct80UnweightedProjection
import Direct80GraphPower
import Direct80ProjectionPell

/-! Bind the entire-product projection to the exact 80 graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80GraphUnweighted
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalProjection
open TenPositive80ProjectionPell Direct80Kpos
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_unweighted (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) : Hnat p v ∣ Knat p v := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hbeta31
  let a : V := A p v-1
  let H : V := Hnat p v
  let C : V := c p v
  let T : V := Exp.exp (rankNat p v)
  obtain ⟨d,z,hd,hn,_hdiv⟩ := graph_projection_pell p v hb hl hh hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hA : 0<A p v := mul_pos (mul_pos hmu hY) (add_pos hX (by simp))
  have hA1 : a+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have h4A : 1≤4*A p v := le_trans (pos_iff_one_le.mp hA) (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1:V)≤4) (by simp : (0:V)≤A p v))
  have hH1 : H+1=4*A p v := tsub_add_cancel_of_le h4A
  have hH : H=4*a+3 := by
    apply add_right_cancel (b:=(1:V))
    calc
      H+1=4*A p v := hH1
      _=4*(a+1) := by rw [hA1]
      _=(4*a+3)+1 := by ring
  have hHcast : (ι H:DiffRing V)=4*ι a+3 := by rw [hH,map_add,map_mul,map_ofNat,map_ofNat]
  have hgap := (graph_positive_gap p v hb hv hz).1
  have hKcast : (ι (3*C-2*X p v):DiffRing V)=3*ι C-2*ι (X p v) := by
    apply eq_sub_iff_add_eq.mpr
    have h2 : (2:DiffRing V)*ι (X p v)=ι (2*X p v) := by rw [map_mul,map_ofNat]
    rw [h2,←map_add]
    change ι ((3*C-2*X p v)+2*X p v)=3*ι C
    rw [tsub_add_cancel_of_le (le_of_lt hgap),map_mul,map_ofNat]
  have hKn : (ι (Knat p v):DiffRing V)=
      (4*ι a+3)*ι (X p v)*ι C-2*(ι (X p v)*ι (X p v)+2*ι a*ι (X p v)*ι C-1) := by
    change (ι (X p v*(3*C-2*X p v)+2):DiffRing V)=_
    rw [map_add,map_mul,map_ofNat,hKcast]
    ring
  have hpower := Direct80GraphPower.graph_power p v hbeta31 hl hh hv hz hbetaodd
  change d=T+a*C+H*z at hd
  have hTX : T=X p v := hpower.symm
  rw [hTX] at hd
  have hdR := congrArg (fun x : V => (ι x:DiffRing V)) hd
  have hnR := congrArg (fun x : V => (ι x:DiffRing V)) hn
  simp only [map_add,map_mul,map_one] at hdR hnR
  rw [hHcast] at hdR hnR
  have hu := Direct80UnweightedProjection.unweighted (ι a:DiffRing V) (ι C) (ι d) (ι (X p v)) (ι z) hdR hnR
  have hdivR : (ι H:DiffRing V) ∣ ι (Knat p v) := by
    rw [hHcast,hKn]
    exact hu
  exact natural_dvd_of_signed H (Knat p v) hdivR

#print axioms Direct80GraphUnweighted.graph_unweighted
end Direct80GraphUnweighted
