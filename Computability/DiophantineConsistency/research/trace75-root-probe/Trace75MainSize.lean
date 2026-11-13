import Trace75MainFive

/-! Main index at least five gives c beyond the third Pell ordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75MainSize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPellHalfIndex
open Trace75Factors Trace75MainFive
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_main_size (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb2 : 2≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ r j I : V, 5≤r ∧ r<j ∧ r%2=1 ∧ 0<j ∧ 0<I ∧
      c p v=ycoord r (A p v-1) ∧ 4*delta p v+3<c p v ∧
      xcoord j (A p v-1)=1+2*(delta p v*U p v*U p v*E p v) ∧
      ycoord j (A p v-1)=I ∧ c p v*c p v∣I := by
  obtain ⟨r,j,I,hr5,hrj,hodd,hj,hI,hc,_,hjx,hjy,hdiv⟩ := graph_main_index_ge_five p v hb2 hv hz
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by simp : (0:V)<2) hb2
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have ha : 0<A p v := add_pos (mul_pos hx hy) hy
  have ha1 : A p v-1+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp ha)
  have hbaseA : A p v-1+2=A p v+1 := by
    calc
      A p v-1+2=(A p v-1+1)+1 := by ring
      _=A p v+1 := by rw [ha1]
  have hy3 : ycoord 3 (A p v-1)=4*delta p v+3 := by
    apply add_right_cancel (b := (1:V))
    calc
      ycoord 3 (A p v-1)+1=4*(A p v-1+2)*(A p v-1+2) := y_three (A p v-1)
      _=4*(A p v+1)*(A p v+1) := by rw [hbaseA]
      _=(4*delta p v+3)+1 := by dsimp [Trace75Factors.delta]; ring
  have hr3 : 3<r := lt_of_lt_of_le (by norm_num : (3:V)<5) hr5
  have hsize : 4*delta p v+3<c p v := by
    rw [←hy3,hc]
    exact (ordinate_strictMono (A p v-1)) hr3
  exact ⟨r,j,I,hr5,hrj,hodd,hj,hI,hc,hsize,hjx,hjy,hdiv⟩

#print axioms Trace75MainSize.graph_main_size
end Trace75MainSize
