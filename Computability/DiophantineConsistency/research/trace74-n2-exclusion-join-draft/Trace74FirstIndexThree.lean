import Trace74N2Exclusion
import Trace74Index

/-! UNCHECKED DRAFT. Every first-Pell index in the same 74 zero is at least 3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FirstIndexThree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Index Trace74N2Exclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_first_index_ge_three (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hq4 : 4≤q p v)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) : 3≤n := by
  have hn2 := first_index_ge_two p v n hb hv hz hcoord
  let P : V := firstParam p v
  let B : V := 2*(P-1)+1
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hP : 0<P := mul_pos hX (mul_pos hY hY)
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
  have hne : n≠2 := by
    intro hn
    rw [hn] at hcoord
    have hsmall : k v=8*P+4 := calc
      k v=2*ycoord 2 B := hcoord.symm
      _=8*P+4 := by rw [hy2,hB]; ring
    exact graph_small_k_impossible p v hb hv hz hq4 hsmall
  have hn : 2<n := lt_of_le_of_ne hn2 (Ne.symm hne)
  simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hn

#print axioms Trace74FirstIndexThree.graph_first_index_ge_three
end Trace74FirstIndexThree
