import Trace74Index
import Trace74OddOrdinateBound

/-! UNCHECKED DRAFT. Discrete first-Pell size gap from a positive trace74 zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FirstPellGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Index Trace74OddOrdinateBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_pell_gap (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    k v=8*firstParam p v+4 ∨
      32*(firstParam p v)^2+32*firstParam p v+6≤k v := by
  obtain ⟨tau,f,n,I,_,_,_,_,_,_,_,hny,_⟩ := first_and_doubled p v hb hv hz
  have hn2 := first_index_ge_two p v n hb hv hz hny
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
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
  have hy3 : 2*ycoord 3 B=32*P^2+32*P+6 := by
    apply add_right_cancel (b:=2)
    calc
      2*ycoord 3 B+2=2*(ycoord 3 B+1) := by ring
      _=2*(4*(B+2)^2) := by rw [ordinate_three]
      _=(32*P^2+32*P+6)+2 := by rw [hB]; ring
  rcases eq_or_lt_of_le hn2 with heq | hlt
  · left
    rw [←heq] at hny
    calc
      k v=2*ycoord 2 B := hny.symm
      _=8*P+4 := by rw [hy2,hB]; ring
  · right
    have hn3 : 3≤n := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hlt
    calc
      32*P^2+32*P+6=2*ycoord 3 B := hy3.symm
      _≤2*ycoord n B := mul_le_mul_of_nonneg_left ((ordinate_strictMono B).monotone hn3) (by simp)
      _=k v := hny

#print axioms Trace74FirstPellGap.graph_first_pell_gap
end Trace74FirstPellGap
