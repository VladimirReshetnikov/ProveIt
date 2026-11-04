import Trace74IndexUpper
import Trace74IndexOrder
import Trace74Index

/-! UNCHECKED DRAFT. Upper-index comparison for the actual 74 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74GraphIndexUpper
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Index Trace74IndexOrder Trace74IndexUpper
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_index_window (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n r : V, 0<n ∧ 0<r ∧ r%2=1 ∧ n<r ∧ r<2*n ∧
      2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      c p v=ycoord r (A p v-1) ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<15) hb15
  obtain ⟨n,r,hn,hr,hodd,hnr,hny,hc,hmod⟩ := graph_ordered_indices p v hb hv hz
  have hn2 : 2≤n := first_index_ge_two p v n hb hv hz hny
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hw : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hq16 : (16:V)≤q p v := by
    unfold q b
    calc
      (16:V)=15*1+1 := by ring
      _≤(p 0:V)*v 0+1 := by
        simpa only [add_comm] using add_le_add_right (mul_le_mul hb15 hj (by simp) (by simp)) 1
  have hX : (16:V)≤X p v := calc
    (16:V)≤q p v := hq16
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (show (0:V)≤q p v by simp)
    _=X p v := rfl
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hP : firstParam p v=X p v*Y p v*Y p v := by dsimp [firstParam]; ring
  have hc' : c p v=ycoord r (Y p v*(X p v+1)-1) := by simpa only [hA] using hc
  have hk' : k v=2*ycoord n (2*(X p v*Y p v*Y p v-1)+1) := by simpa only [hP] using hny.symm
  have hu := upper_of_ordinates (X p v) (Y p v) n r (k v) (c p v) (v 8) (v 9)
    hX hY1 hn2 rfl rfl (hv 9) hc' hk'
  exact ⟨n,r,hn,hr,hodd,hnr,hu,hny,hc,hmod⟩

#print axioms Trace74GraphIndexUpper.graph_index_window
end Trace74GraphIndexUpper
