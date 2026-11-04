import Trace74PellGapBinding
import Trace74NearDiagonalLargeHeightModel
import Trace74UniformGraphHeight
import Trace74IndexOrder
import Trace74NearDiagonalSizeModel

/-! Same-zero near-diagonal contradiction with explicit lower power bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74NearDiagonalGraphJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74PellGapBinding Trace74IndexOrder
open Trace74NearDiagonalHeightModel Trace74NearDiagonalLargeHeightModel Trace74UniformGraphHeight
open Trace74NearDiagonalSizeModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exclude a near-diagonal same-zero index pair, provided the displayed
model-indexed lower power estimate is supplied separately. -/
theorem graph_near_diagonal_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn8 : (8:V)≤n) (hr : r≤n+2)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : c p v=ycoord r (A p v-1))
    (hlarge : 512*(b p v)*(b p v)*(Exp.exp r)*(Exp.exp r)*(Exp.exp r)*(Exp.exp r)<
      power (Y p v) (n-6)) : False := by
  let j : V := n-3
  let s : V := r-1
  let t : V := n-6
  have hn3 : (3:V)≤n := le_trans (by norm_num) hn8
  have hn6 : (6:V)≤n := le_trans (by norm_num) hn8
  have hj : j+3=n := tsub_add_cancel_of_le hn3
  have ht : t+6=n := tsub_add_cancel_of_le hn6
  have hnr : n<r := graph_first_lt_odd p v n r hb hv hny hc
  have hr2 : (2:V)≤r := le_trans (by norm_num : (2:V)≤8) (le_trans hn8 (le_of_lt hnr))
  have hr1 : (1:V)≤r := le_trans (by norm_num) hr2
  have hs : s+1=r := tsub_add_cancel_of_le hr1
  have hsle : s≤j+4 := by
    apply (add_le_add_iff_right (1:V)).mp
    calc
      s+1=r := hs
      _≤n+2 := hr
      _=(j+4)+1 := by rw [←hj]; ring
  have hindex : j+1=t+4 := by
    apply add_right_cancel (b := (2:V))
    calc
      j+1+2=j+3 := by ring
      _=n := hj
      _=t+6 := ht.symm
      _=t+4+2 := by ring
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 1≤Y p v := pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6))
  have hq2 : (2:V)≤q p v := by
    unfold q b
    have hm : 1≤(p 0:V)*v 0 := one_le_mul (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    calc
      (2:V)=1+1 := by norm_num
      _≤(p 0:V)*v 0+1 := by simpa only [add_comm] using add_le_add_right hm 1
  have hX : (2:V)≤X p v := calc
    (2:V)≤q p v := hq2
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (pos_iff_one_le.mp (hv 5)) (show (0:V)≤q p v by simp)
    _=X p v := rfl
  have hgap := tuple_pell_gap p v n r (hv 8) hny hc
  have hgap' : (2*Y p v)*ycoord ((j+2)+1) (2*(X p v*Y p v*Y p v-1)+1)<
      ycoord (s+1) (Y p v*(X p v+1)-1) := by
    have heq : j+2+1=n := by rw [show j+2+1=j+3 by ring,hj]
    simpa only [heq,hs] using hgap
  have hsmall : power (Y p v) (t+4)<8*(X p v)*(X p v) := by
    rw [←hindex]
    exact pell_gap_height (X p v) (Y p v) j s hX hY hsle hgap'
  have hbig : 8*(b p v)*(Exp.exp r)*(Exp.exp r)*(Y p v)*(Y p v)<X p v :=
    amplified_height (X p v) (Y p v) (b p v) (Exp.exp r) t hY hsmall hlarge
  have hbig' : 8*(b p v)*(Exp.exp r)^2*(Y p v)^2<X p v := by
    simpa only [pow_two,mul_assoc] using hbig
  exact graph_height_impossible p v r hb hv hz hr2 hc hbig'

/-- Large q supplies the lower power bound for the same graph tuple. -/
theorem graph_near_diagonal_large_q_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn8 : (8:V)≤n) (hr : r≤n+2) (hq : (1073741824:V)≤q p v)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : c p v=ycoord r (A p v-1)) : False := by
  let d : V := n-8
  have hd : d+8=n := tsub_add_cancel_of_le hn8
  have hd' : d+2=n-6 := by
    apply add_right_cancel (b := (6:V))
    calc
      d+2+6=d+8 := by ring
      _=n := hd
      _=n-6+6 := (tsub_add_cancel_of_le (le_trans (by norm_num : (6:V)≤8) hn8)).symm
  have hr' : r≤d+10 := calc
    r≤n+2 := hr
    _=d+10 := by rw [←hd]; ring
  have hq1 : (1:V)≤q p v := le_trans (by norm_num) hq
  have hy : q p v*q p v≤Y p v := calc
    q p v*q p v≤(q p v*q p v)*q p v := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 (show (0:V)≤q p v*q p v by simp)
    _≤(q p v*q p v*q p v)*v 6 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (show (0:V)≤q p v*q p v*q p v by simp)
    _=Y p v := rfl
  have hh : b p v<q p v := by
    change b p v<b p v+1
    exact lt_add_of_pos_right _ (by norm_num)
  have hlarge := lower_power_bound (q p v) (Y p v) (b p v) (Exp.exp r) d r hq hy hh hr' (power_two r).symm
  rw [hd'] at hlarge
  exact graph_near_diagonal_impossible p v n r hb hv hz hn8 hr hny hc hlarge

#print axioms Trace74NearDiagonalGraphJoin.graph_near_diagonal_impossible
#print axioms Trace74NearDiagonalGraphJoin.graph_near_diagonal_large_q_impossible
end Trace74NearDiagonalGraphJoin
