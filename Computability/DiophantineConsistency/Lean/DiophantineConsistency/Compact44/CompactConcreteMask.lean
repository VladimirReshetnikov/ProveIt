import DiophantineConsistency.Compact44.CompactListMask
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
namespace CompactConcreteMask
open Finset
open scoped BigOperators
open CompactListMask

/-- Concrete support before the forbidden selector is erased. -/
def support : Finset ℕ :=
  ((range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032 ∪
    {1063,1064,1095,2195,3296}) \ {1})

theorem special_mem : 1063 ∈ support := by simp [support]
theorem origin_mem : 0 ∈ support := by simp [support]

theorem support_bounded : support ⊆ range 8807 := by
  intro j hj
  simp only [support, mem_sdiff, mem_union, mem_range, mem_Ico, mem_insert, mem_singleton] at hj
  simp only [mem_range]
  omega

/-- Generic defect-sum expansion. The special slot must be in the support. -/
theorem defect_sum (B len special : ℕ) (S : Finset ℕ)
    (hS : S ⊆ range len) (hs : special ∈ S) :
    (∑ j ∈ range len, defect special S j * B^j) =
      (∑ j ∈ S, B^j) + 2*B^special := by
  have hi : special ∈ range len := hS hs
  have hpoint : ∀ j : ℕ, defect special S j * B^j =
      (if j∈S then B^j else 0) + (if j=special then 2*B^j else 0) := by
    intro j
    by_cases hj : j=special
    · subst j
      simp [defect, hs]
      ring
    · by_cases h : j∈S
      · simp [defect,hj,h]
      · simp [defect,hj,h]
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset hS]
  simp [hi]

/-- Non-expanding exact equality to the finite weighted-support recipe. -/
theorem concrete_recipe :
    Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) =
      (2^67)^8807 - 1 - (∑ j ∈ support, (2^67)^j) - 2*(2^67)^1063 := by
  have h := digits_add_defect (2^67) 8807 1063 support (by norm_num)
  rw [defect_sum _ _ _ _ support_bounded special_mem] at h
  omega
/-- The same symbolic recipe in bit-exponent form used by the coefficient builder. -/
theorem concrete_bit_recipe :
    Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) =
      2^590069 - 1 - (∑ j ∈ support, 2^(67*j)) - 2*2^(67*1063) := by
  simpa only [← pow_mul, show (67:ℕ)*8807=590069 by decide] using concrete_recipe

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_class (j : V) (hj : j < 8807) :
    let M : V := (Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ)
    dig 67 M j = Exp.exp 67-1 ∨ dig 67 M j = Exp.exp 67-2 ∨
      dig 67 M j = Exp.exp 67-4 := by
  exact model_mask_class 8807 1063 support j hj

theorem model_lt :
    ((Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ):V) <
      Exp.exp ((67:V)*8807) := by
  exact model_mask_lt 8807 1063 support

theorem model_origin :
    dig 67 ((Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ):V) 0 =
      Exp.exp 67-2 := by
  exact model_mask_origin 8807 1063 support (by decide) (by decide) origin_mem
end Model
end CompactConcreteMask
#print axioms CompactConcreteMask.concrete_bit_recipe
#print axioms CompactConcreteMask.model_class
#print axioms CompactConcreteMask.model_lt
#print axioms CompactConcreteMask.model_origin
#print axioms CompactConcreteMask.concrete_recipe
