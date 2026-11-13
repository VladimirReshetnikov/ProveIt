import Trace74Fold
import Trace74Pell
import Direct80IndexOne

/-! UNCHECKED DRAFT. Exclude the first Pell index one for an actual trace74 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74Index
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Fold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_index_ge_two (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) : 2≤n := by
  have hkpos : 0<k v := add_pos (hv 8) (hv 9)
  have hn : 0<n := pos_iff_ne_zero.mpr (by
    intro hn0
    apply ne_of_gt hkpos
    simpa [hn0] using hcoord.symm)
  obtain ⟨m,j,I,_,_,_,_,_,hc,_,_,_⟩ := graph_odd_ordinate p v hb hv hz
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY : 1≤Y p v := pos_iff_one_le.mp hy
  have hne : n≠1 := by
    intro h1
    have hy1 : ycoord 1 (2*(firstParam p v-1)+1)=1 := by simpa using y_succ (0:V) _
    have hk : v 8+v 9=2 := by
      rw [h1,hy1] at hcoord
      simpa [k] using hcoord.symm
    apply Direct80IndexOne.impossible (Y p v) (Y p v) (X p v) (v 8) (v 9) m
      hY (le_refl _) (hv 8) (hv 9) hk
    have hA : A p v = Y p v*(X p v+1) := by dsimp [A]; ring
    rw [hA] at hc
    simpa only [c,k] using hc
  have hgt : 1<n := lt_of_le_of_ne (pos_iff_one_le.mp hn) (Ne.symm hne)
  simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp hgt

#print axioms Trace74Index.first_index_ge_two
end Trace74Index
