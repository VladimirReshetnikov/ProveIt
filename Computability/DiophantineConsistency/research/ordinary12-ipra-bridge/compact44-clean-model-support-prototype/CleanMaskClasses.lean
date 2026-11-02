import DiophantineConsistency.CleanGeometry
import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactConcreteMask
import DiophantineConsistency.ArithmeticStandardCasts
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CleanMaskClasses
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits CompactSymbolicPorts CompactListMask
open DiophantineConsistency.ArithmeticMaskConstants
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem support_subset_bad (j : ℕ) (hj : j∈CompactConcreteMask.support) : CleanGeometry.BadNat j := by
  simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hj
  unfold CleanGeometry.BadNat
  omega

private theorem sub_cast (r : ℕ) (hr : r ≤ 2^67) :
    ((2^67-r : ℕ):V)=Exp.exp (67:V)-(r:V) := by
  have h1 : 2^67-r+r=2^67 := Nat.sub_add_cancel hr
  have h2 : ((2^67-r : ℕ):V)+(r:V)=((2^67:ℕ):V) := by exact_mod_cast h1
  have h3 : ((2^67:ℕ):V)=Exp.exp (67:V) := by simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 67).symm
  rw [h3] at h2
  exact eq_tsub_of_add_eq h2

theorem ordinary_mask_digit (j : ℕ) (hj : j<8807)
    (hmem : j∈CompactConcreteMask.support) (hspecial : j≠1063) :
    dig 67 (lowNat:V) (j:V)=Exp.exp 67-2 := by
  have hd := dig_ofDigits (V:=V) 67 (digits (2^67) 8807 1063 CompactConcreteMask.support)
    (digits_lt _ _ _ _ (by norm_num)) j
  rw [digits_getD _ _ _ _ hj] at hd
  simp only [digit, if_neg hspecial, if_pos hmem] at hd
  rw [sub_cast 2 (by norm_num)] at hd
  exact hd

theorem absent_mask_digit (j : ℕ) (hj : j<8807)
    (hmem : j∉CompactConcreteMask.support) (hspecial : j≠1063) :
    dig 67 (lowNat:V) (j:V)=Exp.exp 67-1 := by
  have hd := dig_ofDigits (V:=V) 67 (digits (2^67) 8807 1063 CompactConcreteMask.support)
    (digits_lt _ _ _ _ (by norm_num)) j
  rw [digits_getD _ _ _ _ hj] at hd
  simp only [digit, if_neg hspecial, if_neg hmem] at hd
  rw [sub_cast 1 (by norm_num)] at hd
  simp only [Nat.cast_one] at hd
  exact hd
#print axioms CleanMaskClasses.support_subset_bad
#print axioms CleanMaskClasses.ordinary_mask_digit
#print axioms CleanMaskClasses.absent_mask_digit
end CleanMaskClasses
