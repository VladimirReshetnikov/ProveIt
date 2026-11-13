import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCopy
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem empty_copy (A W : V) (hW : W<A) (hdiv : A∣W) : W=0 := by
  by_contra hn
  have hWp : 0<W := pos_iff_ne_zero.mpr hn
  exact (not_le_of_gt hW) (Arithmetic.le_of_dvd hWp hdiv)

theorem selected_copy (A v W : V) (hv : 0<v) (hvA : v<A) (hWA : W<A)
    (hdiv : A∣A-v+W) : W=v := by
  have hAmv : 0<A-v := tsub_pos_iff_lt.mpr hvA
  have hP : 0<A-v+W := lt_of_lt_of_le hAmv (le_add_self)
  have hPA : A-v+W<2*A := by
    have hsub : A-v<A := tsub_lt_self (lt_trans hv hvA) hv
    have h := add_lt_add hsub hWA
    simpa only [two_mul] using h
  obtain ⟨k,hk⟩ := hdiv
  have hk0 : 0<k := by
    by_contra hn
    have hz : k=0 := le_antisymm (not_lt.mp hn) (by simp)
    rw [hz,mul_zero] at hk
    exact (ne_of_gt hP) hk
  have hk2 : k<2 := by
    by_contra hn
    have hle : 2≤k := not_lt.mp hn
    have hmul : A*2≤A*k := mul_le_mul_of_nonneg_left hle (by simp)
    rw [←hk] at hmul
    have : 2*A≤A-v+W := by simpa only [mul_comm] using hmul
    exact (not_le_of_gt hPA) this
  have hk1 : k=1 := le_antisymm (lt_succ_iff_le.mp (by simpa using hk2)) (pos_iff_one_le.mp hk0)
  rw [hk1,mul_one] at hk
  have he : (A-v)+W=(A-v)+v := by
    rw [tsub_add_cancel_of_le (le_of_lt hvA)]
    exact hk
  exact add_left_cancel he
end CompactCopy
#print axioms CompactCopy.empty_copy
#print axioms CompactCopy.selected_copy
