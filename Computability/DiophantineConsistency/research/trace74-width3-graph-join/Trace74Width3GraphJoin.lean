import Trace74PellGapBinding
import Trace74Width3PellHeightModel
import Trace74Width3AmplificationModel
import Trace74UniformGraphHeight
import Trace74IndexOrder
import Trace74Width3SizeModel

/-! Same-zero near-diagonal contradiction with explicit lower power bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74Width3GraphJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74PellGapBinding Trace74IndexOrder
open Trace74Width3PellHeightModel Trace74Width3AmplificationModel Trace74UniformGraphHeight
open Trace74Width3SizeModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exclude a near-diagonal same-zero index pair, provided the displayed
model-indexed lower power estimate is supplied separately. -/
theorem graph_width3_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn12 : (12:V)≤n) (hr : r≤n+3)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : c p v=ycoord r (A p v-1))
    (hlarge : 16384*(b p v)*(b p v)*(b p v)*(Exp.exp r)*(Exp.exp r)*(Exp.exp r)*(Exp.exp r)*(Exp.exp r)*(Exp.exp r)<
      power (Y p v) (n-9)) : False := by
  let j : V := n-4
  let s : V := r-1
  let t : V := n-9
  have hn4 : (4:V)≤n := le_trans (by norm_num) hn12
  have hn9 : (9:V)≤n := le_trans (by norm_num) hn12
  have hj : j+4=n := tsub_add_cancel_of_le hn4
  have ht : t+9=n := tsub_add_cancel_of_le hn9
  have hnr : n<r := graph_first_lt_odd p v n r hb hv hny hc
  have hr2 : (2:V)≤r := le_trans (by norm_num : (2:V)≤12) (le_trans hn12 (le_of_lt hnr))
  have hr1 : (1:V)≤r := le_trans (by norm_num) hr2
  have hs : s+1=r := tsub_add_cancel_of_le hr1
  have hsle : s≤j+6 := by
    apply (add_le_add_iff_right (1:V)).mp
    calc
      s+1=r := hs
      _≤n+3 := hr
      _=(j+6)+1 := by rw [←hj]; ring
  have hindex : j+1=t+6 := by
    apply add_right_cancel (b := (3:V))
    calc
      j+1+3=j+4 := by ring
      _=n := hj
      _=t+9 := ht.symm
      _=t+6+3 := by ring
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
  have hgap' : (2*Y p v)*ycoord ((j+3)+1) (2*(X p v*Y p v*Y p v-1)+1)<
      ycoord (s+1) (Y p v*(X p v+1)-1) := by
    have heq : j+3+1=n := by rw [show j+3+1=j+4 by ring,hj]
    simpa only [heq,hs] using hgap
  have hsmall : power (Y p v) (t+6)<32*(X p v)*(X p v)*(X p v) := by
    rw [←hindex]
    exact pell_gap_height (X p v) (Y p v) j s hX hY hsle hgap'
  have hbig : 8*(b p v)*(Exp.exp r)*(Exp.exp r)*(Y p v)*(Y p v)<X p v :=
    amplified_height (X p v) (Y p v) (b p v) (Exp.exp r) t hY hsmall hlarge
  have hbig' : 8*(b p v)*(Exp.exp r)^2*(Y p v)^2<X p v := by
    simpa only [pow_two,mul_assoc] using hbig
  exact graph_height_impossible p v r hb hv hz hr2 hc hbig'

/-- Large q supplies the lower power bound for the same graph tuple. -/
theorem graph_width3_large_q_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn12 : (12:V)≤n) (hr : r≤n+3) (hq : (1073741824:V)≤q p v)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : c p v=ycoord r (A p v-1)) : False := by
  let d : V := n-12
  have hd : d+12=n := tsub_add_cancel_of_le hn12
  have hd' : d+3=n-9 := by
    apply add_right_cancel (b := (9:V))
    calc
      d+3+9=d+12 := by ring
      _=n := hd
      _=n-9+9 := (tsub_add_cancel_of_le (le_trans (by norm_num : (9:V)≤12) hn12)).symm
  have hr' : r≤d+15 := calc
    r≤n+3 := hr
    _=d+15 := by rw [←hd]; ring
  have hy : q p v*q p v*q p v≤Y p v := by
    simpa only [Y,mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6)) (show (0:V)≤q p v*q p v*q p v by simp)
  have hh : b p v<q p v := by
    change b p v<b p v+1
    exact lt_add_of_pos_right _ (by norm_num)
  have hlarge := lower_power_bound (q p v) (Y p v) (b p v) (Exp.exp r) d r hq hy hh hr' (power_two r).symm
  rw [hd'] at hlarge
  exact graph_width3_impossible p v n r hb hv hz hn12 hr hny hc hlarge

#print axioms Trace74Width3GraphJoin.graph_width3_impossible
#print axioms Trace74Width3GraphJoin.graph_width3_large_q_impossible
end Trace74Width3GraphJoin
