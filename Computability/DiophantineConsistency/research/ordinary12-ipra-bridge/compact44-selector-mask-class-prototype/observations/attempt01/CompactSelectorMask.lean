import DiophantineConsistency.CompactPositionGraph
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSelectorMask
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits CompactSymbolicPorts
open CompactListMask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem sub_cast (r : ℕ) (hr : r ≤ 2^67) :
    ((2^67-r : ℕ):V)=Exp.exp (67:V)-(r:V) := by
  have h1 : 2^67-r+r=2^67 := Nat.sub_add_cancel hr
  have h2 : ((2^67-r : ℕ):V)+(r:V)=((2^67:ℕ):V) := by exact_mod_cast h1
  have h3 : ((2^67:ℕ):V)=Exp.exp (67:V) := by simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 67).symm
  rw [h3] at h2
  exact eq_tsub_of_add_eq h2

theorem selector_mask_digit (j : ℕ) (hj : j<943) (hne : j≠1) :
    dig 67 (lowNat:V) (j:V)=Exp.exp 67-2 := by
  have hj' : j<8807 := by omega
  have hmem : j∈CompactConcreteMask.support := by
    simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union, Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨Or.inl (Or.inl (Or.inl (Or.inl hj))), by simpa using hne⟩
  have hspecial : j≠1063 := by omega
  have hd := dig_ofDigits (V:=V) 67 (digits (2^67) 8807 1063 CompactConcreteMask.support)
    (digits_lt _ _ _ _ (by norm_num)) j
  rw [digits_getD _ _ _ _ hj'] at hd
  simp only [digit, if_neg hspecial, if_pos hmem] at hd
  rw [sub_cast 2 (by norm_num)] at hd
  exact hd

theorem forbidden_mask_digit : dig 67 (lowNat:V) (1:V)=Exp.exp 67-1 := by
  have hmem : (1:ℕ)∉CompactConcreteMask.support := by simp [CompactConcreteMask.support]
  have hd := dig_ofDigits (V:=V) 67 (digits (2^67) 8807 1063 CompactConcreteMask.support)
    (digits_lt _ _ _ _ (by norm_num)) 1
  rw [digits_getD _ _ _ _ (by norm_num)] at hd
  simp only [digit, if_neg (by norm_num : (1:ℕ)≠1063), if_neg hmem] at hd
  rw [sub_cast 1 (by norm_num)] at hd
  exact hd

end CompactSelectorMask
#print axioms CompactSelectorMask.selector_mask_digit
#print axioms CompactSelectorMask.forbidden_mask_digit
