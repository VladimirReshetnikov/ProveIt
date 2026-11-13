import Trace74N2FifthGrowth
import Trace74Fold
import Trace74Pell

/-! UNCHECKED DRAFT. n=2 forces the same graph odd ordinate to be index 3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74N2OddThree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Fold Trace74N2FifthGrowth
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_small_k_odd_three (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hsmall : k v=8*firstParam p v+4) :
    c p v=ycoord 3 (A p v-1) := by
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hη : v 8<k v := by
    change v 8<v 8+v 9
    exact lt_add_of_pos_right _ (hv 9)
  have hc_upper : c p v<(8*X p v*(Y p v*Y p v)+4)*(Y p v+1) := by
    calc
      c p v=k v*Y p v+v 8 := rfl
      _<k v*Y p v+k v := by simpa only [add_comm] using add_lt_add_left hη (k v*Y p v)
      _=k v*(Y p v+1) := by ring
      _=(8*X p v*(Y p v*Y p v)+4)*(Y p v+1) := by rw [hsmall]; dsimp [firstParam]; ring
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hfifth : (8*X p v*(Y p v*Y p v)+4)*(Y p v+1)<ycoord 5 (A p v-1) := by
    rw [hA]
    exact ordinate_five_exceeds_small_k (X p v) (Y p v) hX hY
  have hc2 : 2<c p v := by
    have hk2 : 2≤k v := by
      simpa only [k,show (2:V)=1+1 by ring] using
        _root_.add_le_add (pos_iff_one_le.mp (hv 8)) (pos_iff_one_le.mp (hv 9))
    have hkY : k v≤k v*Y p v := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v)
    exact lt_of_le_of_lt (le_trans hk2 hkY) (by
      change k v*Y p v<k v*Y p v+v 8
      exact lt_add_of_pos_right _ (hv 8))
  obtain ⟨r,j,I,hr,hrj,hodd,hj,hI,hc,hx,hy,hdiv⟩ := graph_odd_ordinate p v hb hv hz
  have hrlt5 : r<5 := by
    by_contra hn
    have hle : 5≤r := le_of_not_gt hn
    have hy5 : ycoord 5 (A p v-1)≤c p v := by
      rw [hc]
      exact (ordinate_strictMono (A p v-1)).monotone hle
    exact (not_lt_of_ge hy5) (lt_trans hc_upper hfifth)
  have hrne1 : r≠1 := by
    intro he
    rw [he] at hc
    have hy1 : ycoord 1 (A p v-1)=1 := by simpa using y_succ (0:V) (A p v-1)
    rw [hy1] at hc
    rw [hc] at hc2
    exact (not_lt_of_ge (by simp : (2:V)≥1)) hc2
  have h1r : 1<r := lt_of_le_of_ne (pos_iff_one_le.mp hr) (Ne.symm hrne1)
  have hr2 : 2≤r := by simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp h1r
  have hrne2 : r≠2 := by intro he; rw [he] at hodd; norm_num at hodd
  have h2r : 2<r := lt_of_le_of_ne hr2 (Ne.symm hrne2)
  have hr3 : 3≤r := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp h2r
  have heq : r=3 := by
    by_contra hn
    have h3r : 3<r := lt_of_le_of_ne hr3 (Ne.symm hn)
    have hr4 : 4≤r := by simpa only [show (3:V)+1=4 by ring] using lt_iff_succ_le.mp h3r
    have hrne4 : r≠4 := by
      intro he
      rw [he,show (4:V)=2*2 by ring,mod_mul_self_right] at hodd
      exact zero_ne_one hodd
    have h4r : 4<r := lt_of_le_of_ne hr4 (Ne.symm hrne4)
    have hr5 : 5≤r := by simpa only [show (4:V)+1=5 by ring] using lt_iff_succ_le.mp h4r
    exact (not_le_of_gt hrlt5) hr5
  simpa only [heq] using hc

#print axioms Trace74N2OddThree.graph_small_k_odd_three
end Trace74N2OddThree
