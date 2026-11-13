import Trace74Fold

/-! UNCHECKED DRAFT. A graph-zero consequence; no individual F/C bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74OddOrdinateBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence Trace75Factors Trace74Fold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ordinate_three (b : V) : ycoord 3 b+1=4*(b+2)^2 := by
  have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
  have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
  have hx2 : xcoord 2 b=(b+2)*(b+2)+ArithmeticPellRecurrence.delta b := by
    calc
      xcoord 2 b=(b+2)*xcoord 1 b+ArithmeticPellRecurrence.delta b*ycoord 1 b := by
        simpa only [show (1:V)+1=2 by ring] using x_succ (1:V) b
      _=(b+2)*(b+2)+ArithmeticPellRecurrence.delta b := by rw [hx1,hy1]; ring
  have hy2 : ycoord 2 b=2*(b+2) := by
    calc
      ycoord 2 b=xcoord 1 b+(b+2)*ycoord 1 b := by
        simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) b
      _=2*(b+2) := by rw [hx1,hy1]; ring
  have hy3 : ycoord 3 b=xcoord 2 b+(b+2)*ycoord 2 b := by
    simpa only [show (2:V)+1=3 by ring] using y_succ (2:V) b
  rw [hy3,hx2,hy2]
  unfold ArithmeticPellRecurrence.delta
  ring

theorem graph_ordinate_lower (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    4*(A p v+1)^2≤c p v+1 := by
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hA : 0<A p v := by
    change 0<X p v*Y p v+Y p v
    exact add_pos (mul_pos hX hY) hY
  have hA1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have hk2 : 2≤k v := by
    simpa only [k,show (2:V)=1+1 by ring] using
      _root_.add_le_add (pos_iff_one_le.mp (hv 8)) (pos_iff_one_le.mp (hv 9))
  have hkY : k v≤k v*Y p v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hY) (by simp : (0:V)≤k v)
  have hc2 : 2<c p v := lt_of_le_of_lt (le_trans hk2 hkY) (by
    change k v*Y p v<k v*Y p v+v 8
    exact lt_add_of_pos_right _ (hv 8))
  obtain ⟨r,j,I,hr,hrj,hodd,hj,hI,hc,hx,hy,hdiv⟩ := graph_odd_ordinate p v hb hv hz
  have hr1 : 1≤r := pos_iff_one_le.mp hr
  have hrne1 : r≠1 := by
    intro he
    rw [he] at hc
    have hy1 : ycoord 1 (A p v-1)=1 := by simpa using y_succ (0:V) (A p v-1)
    rw [hy1] at hc
    rw [hc] at hc2
    exact (not_lt_of_ge (by simp : (2:V)≥1)) hc2
  have h1r : 1<r := lt_of_le_of_ne hr1 (Ne.symm hrne1)
  have hr2 : 2≤r := by simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp h1r
  have hrne2 : r≠2 := by
    intro he
    rw [he] at hodd
    norm_num at hodd
  have h2r : 2<r := lt_of_le_of_ne hr2 (Ne.symm hrne2)
  have hr3 : 3≤r := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp h2r
  have hle : ycoord 3 (A p v-1)≤c p v := by
    rw [hc]
    exact (ordinate_strictMono (A p v-1)).monotone hr3
  have heq : (A p v-1)+2=A p v+1 := by
    calc
      (A p v-1)+2=((A p v-1)+1)+1 := by ring
      _=A p v+1 := by rw [hA1]
  calc
    4*(A p v+1)^2= ycoord 3 (A p v-1)+1 := by
      rw [ordinate_three,heq]
    _≤c p v+1 := add_le_add_right hle 1

#print axioms Trace74OddOrdinateBound.ordinate_three
#print axioms Trace74OddOrdinateBound.graph_ordinate_lower
end Trace74OddOrdinateBound
