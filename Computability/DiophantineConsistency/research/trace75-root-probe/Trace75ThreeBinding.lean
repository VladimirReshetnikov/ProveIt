import Trace75Index
import Trace75ThreeLarge

/-! An actual trace75 zero at main index three has first index two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75ThreeBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace75Pell Trace75Index
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_index_eq_two_of_main_three (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hfirst : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 3 (A p v-1)) : n=2 := by
  have hn2 := first_index_ge_two p v n hb hv hz hfirst
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
  have hq2 : 2≤q p v := by
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hq1 : 1≤q p v := le_trans (by simp : (1:V)≤2) hq2
  have hw1 : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hs1 : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hX : 2≤X p v := le_trans hq2 (by
    change q p v≤v 5*q p v
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (show (0:V)≤q p v by simp))
  have hY : 2≤Y p v := le_trans hq2 (by
    change q p v≤(q p v*q p v*q p v)*v 6
    calc
      q p v≤q p v*q p v := le_mul_of_one_le_right (by simp) hq1
      _≤(q p v*q p v)*q p v := le_mul_of_one_le_right (by simp) hq1
      _≤(q p v*q p v*q p v)*v 6 := le_mul_of_one_le_right (by simp) hs1)
  have hnnot : ¬3≤n := by
    intro hn3
    apply Trace75ThreeLarge.impossible (X p v) (Y p v) (k v) (v 8) n hX hY (hv 8) hn3
    · simpa only [firstParam] using hfirst
    · simpa only [c,A] using hmain
  have hnlt : n<3 := lt_of_not_ge hnnot
  have hnle : n≤2 := lt_succ_iff_le.mp (by
    simpa only [show (2:V)+1=3 by ring] using hnlt)
  exact le_antisymm hnle hn2

#print axioms Trace75ThreeBinding.first_index_eq_two_of_main_three
end Trace75ThreeBinding
