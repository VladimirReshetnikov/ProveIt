import DiophantineConsistency.BFS943.Trace75Fold

/-! The recovered odd main Pell index is at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75MainIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open Trace75Factors Trace75Fold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_main_index (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ r j I : V, 3≤r ∧ r<j ∧ r%2=1 ∧ 0<j ∧ 0<I ∧
      c p v=ycoord r (A p v-1) ∧ 2*r<c p v ∧
      xcoord j (A p v-1)=1+2*(delta p v*U p v*U p v*E p v) ∧
      ycoord j (A p v-1)=I ∧ c p v*c p v∣I := by
  obtain ⟨r,j,I,hr,hrj,hodd,hj,hI,hc,hjx,hjy,hdiv⟩ := graph_odd_ordinate p v hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hCgt : 1<c p v := lt_of_le_of_lt (pos_iff_one_le.mp (mul_pos hk hY))
    (show k v*Y p v<k v*Y p v+v 8 from lt_add_of_pos_right _ (hv 8))
  have hr1 : 1<r := by
    by_contra hn
    have hrle : r≤1 := le_of_not_gt hn
    have hrone : r=1 := le_antisymm hrle (pos_iff_one_le.mp hr)
    have hy1 : ycoord 1 (A p v-1)=1 := by simpa using y_succ (0:V) (A p v-1)
    rw [hrone,hy1] at hc
    exact (ne_of_gt hCgt) hc
  have hr2 : 2≤r := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hr1
  have hr2lt : 2<r := by
    rcases lt_or_eq_of_le hr2 with h|h
    · exact h
    · rw [←h] at hodd
      simp at hodd
  have hr3 : 3≤r := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hr2lt
  have hrsize : 2*r<c p v := by rw [hc]; exact twice_index_lt_y (A p v-1) r hr3
  exact ⟨r,j,I,hr3,hrj,hodd,hj,hI,hc,hrsize,hjx,hjy,hdiv⟩

#print axioms Trace75MainIndex.graph_main_index
end Trace75MainIndex
