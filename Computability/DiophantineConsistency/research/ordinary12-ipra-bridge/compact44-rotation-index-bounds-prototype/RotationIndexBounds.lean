import DiophantineConsistency.RotationAllCases
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationIndexBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem q_lt (n s : V) (hs : s<67*n) : s/67<n := by
  apply div_lt_of_lt_mul
  simpa only [mul_comm] using hs

theorem no_wrap_source_lt (n e k s : V) (hk : k<n) (heq : 67*k=e+s) : s<67*n := by
  have hb : 67*k<67*n := mul_lt_mul_of_pos_left hk (by norm_num)
  have hs : s≤67*k := by rw [heq]; exact le_add_of_nonneg_left (by simp)
  exact lt_of_le_of_lt hs hb

theorem wrap_source_lt (n e k : V) (he : e<67*n) (hb : 67*k<e) :
    67*n-e+67*k<67*n := by
  calc
    67*n-e+67*k < 67*n-e+e := (add_lt_add_iff_left _).mpr hb
    _ = 67*n := tsub_add_cancel_of_le (le_of_lt he)

theorem reduced_cut_lt (n E : V) (hn : 0<n) : E % (67*n) < 67*n :=
  mod_lt _ (mul_pos (by norm_num) hn)

theorem last_digit_zero (X n : V) (hX : X<Exp.exp (67*n)) : dig 67 X n=0 := by
  unfold dig
  rw [div_eq_zero_of_lt _ hX, zero_mod]

theorem next_in_range_or_zero (X n q : V) (hq : q<n) (hX : X<Exp.exp (67*n)) :
    q+1<n ∨ (q+1=n ∧ dig 67 X (q+1)=0) := by
  by_cases h : q+1<n
  · exact Or.inl h
  · right
    have he : q+1=n := le_antisymm (lt_iff_succ_le.mp hq) (not_lt.mp h)
    exact ⟨he,by rw [he]; exact last_digit_zero X n hX⟩
#print axioms RotationIndexBounds.q_lt
#print axioms RotationIndexBounds.no_wrap_source_lt
#print axioms RotationIndexBounds.wrap_source_lt
#print axioms RotationIndexBounds.reduced_cut_lt
#print axioms RotationIndexBounds.last_digit_zero
#print axioms RotationIndexBounds.next_in_range_or_zero
end RotationIndexBounds
