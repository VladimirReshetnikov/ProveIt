import Trace74UniformProjectionGraph
import Trace74UniformHeightContradiction

/-! Conditional same-graph projection contradiction at arbitrary internal indices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74UniformGraphHeight
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74UniformProjectionGraph Trace74UniformHeightContradiction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The explicit exponential height inequality cannot hold at a positive
trace74 zero with the same main ordinate. No index window is assumed. -/
theorem graph_height_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hr : (2:V)≤r) (hc : c p v=ycoord r (A p v-1))
    (hheight : 8*(b p v)*(Exp.exp r)^2*(Y p v)^2<X p v) : False := by
  let h : DiffRing V := ι (b p v)
  let X0 : DiffRing V := ι (X p v)
  let Y0 : DiffRing V := ι (Y p v)
  let L : DiffRing V := ι (Exp.exp (r-2))
  let K : DiffRing V := ι (Exp.exp r)
  have hdisc : ∀ t : DiffRing V, 0<t → 1≤t := fun _ ht => one_le_of_pos (fun _ hu => pos_iff_one_le.mp hu) ht
  have hh : 0<h := by
    dsimp [h,b]
    simpa only [map_zero] using (ι_lt_ι.mpr (mul_pos hb (hv 0)))
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 1≤Y0 := by
    have hy : 1≤Y p v := pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6))
    dsimp [Y0]
    simpa only [map_one] using (ι_le_ι.mpr hy)
  have hL : 1≤L := by
    dsimp [L]
    simpa only [map_one] using (ι_le_ι.mpr (one_le_exp (r-2)))
  have hrsub : r-2+2=r := tsub_add_cancel_of_le hr
  have hrsub' : (r-2+1)+1=r := by
    calc
      (r-2+1)+1=r-2+2 := by ring
      _=r := hrsub
  have hexp : Exp.exp r=4*Exp.exp (r-2) := by
    calc
      Exp.exp r=Exp.exp ((r-2+1)+1) := congrArg _ hrsub'.symm
      _=4*Exp.exp (r-2) := by rw [exp_succ,exp_succ]; ring
  have hK : K=4*L := by dsimp [K,L]; rw [hexp]; simp only [map_mul,map_ofNat]
  have hheight' : 8*h*K^2*Y0^2<X0 := by
    dsimp [h,K,Y0,X0]
    simpa only [map_mul,map_pow,map_ofNat] using (ι_lt_ι.mpr hheight)
  have hd := graph_reduced p v r hb hv hz hr hc
  change (4*Y0*(X0+1)-1) ∣ h*(4*Y0-1)*(4*(4*L+1)*Y0-1)*((4*L-1)*Y0-L) at hd
  rw [←hK] at hd
  exact projection_impossible h X0 Y0 K L hdisc hh hY hL hK hheight' hd

/-- Every positive zero and supplied main ordinate satisfies the complementary
uniform height bound, without assuming any first-index or height inequality. -/
theorem graph_height_upper (p : Fin 4 → ℕ) (v : Fin 10 → V) (r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hr : (2:V)≤r) (hc : c p v=ycoord r (A p v-1)) :
    X p v≤8*(b p v)*(Exp.exp r)^2*(Y p v)^2 := by
  apply le_of_not_gt
  exact graph_height_impossible p v r hb hv hz hr hc

#print axioms Trace74UniformGraphHeight.graph_height_impossible
#print axioms Trace74UniformGraphHeight.graph_height_upper
end Trace74UniformGraphHeight
