import Trace74NearDiagonalPellModel
import Trace74GraphIndexUpper

/-! Bind the represented Pell growth estimate to one trace74 tuple. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74PellGapBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74GraphIndexUpper Trace74NearDiagonalPellModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The ordinary strict Pell gap is forced by the positive offset in `c`.
Both ordinate equations and the positivity refer to the very same tuple. -/
theorem tuple_pell_gap (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hv8 : 0<v 8)
    (hn : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hr : c p v=ycoord r (A p v-1)) :
    (2*Y p v)*ycoord n (2*(X p v*Y p v*Y p v-1)+1)<
      ycoord r (Y p v*(X p v+1)-1) := by
  have hA : A p v=Y p v*(X p v+1) := by dsimp [A]; ring
  have hP : firstParam p v=X p v*Y p v*Y p v := by dsimp [firstParam]; ring
  have hlt : k v*Y p v<c p v := by
    change k v*Y p v<k v*Y p v+v 8
    exact lt_add_of_pos_right _ hv8
  rw [←hn,hr,hA,hP] at hlt
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hlt

/-- Shift positive indices to apply the represented variable-power sandwich. -/
theorem tuple_power_gap (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hX : 2≤X p v) (hY : 1≤Y p v) (hn1 : 1≤n) (hr1 : 1≤r)
    (hv8 : 0<v 8)
    (hn : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hr : c p v=ycoord r (A p v-1)) :
    (2*Y p v)*power (X p v*(2*Y p v)*(2*Y p v)) (n-1)<
      power (2*X p v*(2*Y p v)) (r-1) := by
  have hn' : n-1+1=n := tsub_add_cancel_of_le hn1
  have hr' : r-1+1=r := tsub_add_cancel_of_le hr1
  apply trace74_strict_power_gap (X p v) (Y p v) (n-1) (r-1) hX hY
  simpa only [hn',hr'] using tuple_pell_gap p v n r hv8 hn hr

/-- An actual positive zero has a same-witness power gap and linked index window. -/
theorem graph_window_power_gap (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb15 : (15:V)≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 0<n ∧ 0<r ∧ r%2=1 ∧ n<r ∧ r<2*n ∧
      2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      c p v=ycoord r (A p v-1) ∧
      (2*Y p v)*power (X p v*(2*Y p v)*(2*Y p v)) (n-1)<
        power (2*X p v*(2*Y p v)) (r-1) := by
  obtain ⟨n,r,hn0,hr0,hodd,hnr,hr2,hn,hr,_⟩ := graph_index_window p v hb15 hv hz
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<15) hb15
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 1≤Y p v := pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6))
  have hq2 : (2:V)≤q p v := by
    unfold q b
    have hm : 1≤(p 0:V)*v 0 := one_le_mul (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    calc
      (2:V)=1+1 := by norm_num
      _≤(p 0:V)*v 0+1 := by simpa only [add_comm] using add_le_add_right hm 1
  have hX : (2:V)≤X p v := calc
    (2:V)≤q p v := hq2
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (pos_iff_one_le.mp (hv 5)) (show (0:V)≤q p v by simp)
    _=X p v := rfl
  exact ⟨n,r,hn0,hr0,hodd,hnr,hr2,hn,hr,
    tuple_power_gap p v n r hX hY (pos_iff_one_le.mp hn0) (pos_iff_one_le.mp hr0) (hv 8) hn hr⟩

#print axioms Trace74PellGapBinding.tuple_pell_gap
#print axioms Trace74PellGapBinding.tuple_power_gap
#print axioms Trace74PellGapBinding.graph_window_power_gap
end Trace74PellGapBinding
