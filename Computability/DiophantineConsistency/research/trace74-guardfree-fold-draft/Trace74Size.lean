import Trace74Index

/-! UNCHECKED DRAFT. First-index and radix lower bounds for trace74. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74Size
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Index
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_rank_size (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) : 8*firstParam p v+4≤k v ∧ 2*(q p v)^4<c p v := by
  obtain ⟨tau,f,n,I,_,_,_,_,_,_,_,hny,_⟩ := first_and_doubled p v hb hv hz
  have hn2 := first_index_ge_two p v n hb hv hz hny
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hy
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hP : 0<P := mul_pos hx (mul_pos hy hy)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : B+2=2*P+1 := by
    calc
      B+2=2*(P-1+1)+1 := by dsimp [B]; ring
      _=2*P+1 := by rw [hP1]
  have hy1 : ycoord 1 B=1 := by simpa using y_succ (0:V) B
  have hx1 : xcoord 1 B=B+2 := by simpa using x_succ (0:V) B
  have hy2 : ycoord 2 B=2*(B+2) := by
    calc
      ycoord 2 B=xcoord 1 B+(B+2)*ycoord 1 B := by
        simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) B
      _=2*(B+2) := by rw [hx1,hy1]; ring
  have hklower : 8*P+4≤k v := calc
    8*P+4=2*ycoord 2 B := by rw [hy2,hB]; ring
    _≤2*ycoord n B := mul_le_mul_of_nonneg_left ((ordinate_strictMono B).monotone hn2) (by simp)
    _=k v := hny
  have hXP : X p v≤P := by
    change X p v≤X p v*(Y p v*Y p v)
    exact le_mul_of_one_le_right (by simp) (one_le_mul hY1 hY1)
  have hw : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hqX : q p v≤X p v := by
    change q p v≤v 5*q p v
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (show (0:V)≤q p v by simp)
  have hqP : q p v≤P := le_trans hqX hXP
  have h2qk : 2*q p v≤k v := calc
    2*q p v≤2*P := mul_le_mul_of_nonneg_left hqP (by simp)
    _≤8*P := mul_le_mul_of_nonneg_right (by norm_num : (2:V)≤8) (by simp)
    _≤8*P+4 := by simp
    _≤k v := hklower
  have hs : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hq3Y : q p v*q p v*q p v≤Y p v := by
    change q p v*q p v*q p v≤(q p v*q p v*q p v)*v 6
    exact le_mul_of_one_le_right (by simp) hs
  have hbound : 2*(q p v)^4<c p v := calc
    2*(q p v)^4=(2*q p v)*(q p v*q p v*q p v) := by ring
    _≤k v*Y p v := mul_le_mul h2qk hq3Y (by simp) (by simp)
    _<k v*Y p v+v 8 := lt_add_of_pos_right _ (hv 8)
  exact ⟨hklower,hbound⟩

#print axioms Trace74Size.graph_rank_size
end Trace74Size
