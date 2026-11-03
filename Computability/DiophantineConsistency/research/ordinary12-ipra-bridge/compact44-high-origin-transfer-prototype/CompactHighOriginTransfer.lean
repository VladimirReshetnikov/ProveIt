import DiophantineConsistency.ArithmeticPackingBlocks

/-! Conditional high-mask origin transfer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactHighOriginTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- If the input has two low zero bits and the mask ends in binary 100,
subtracting one from the mask preserves an already established no-carry fact. -/
theorem transfer_parts (a b : V) (h : NoCarry (4*a) (8*b+4)) :
    NoCarry (4*a) (8*b+3) := by
  have h0 : NoCarry (2*(2*a)+0) (2*(2*(2*b+1))+0) := by
    convert h using 1 <;> ring
  have h1 := (noCarry_binary (2*a) (2*(2*b+1)) 0 0 (by simp) (by simp)).mp h0
  have h2 := (noCarry_binary a (2*b+1) 0 0 (by simp) (by simp)).mp (by simpa using h1.2)
  have hr : a % 2 ≤ 1 := lt_two_iff_le_one.mp (mod_lt a (by norm_num))
  have ha : 2*(a/2)+a%2 = a := by simpa using div_add_mod a 2
  have h3 := (noCarry_binary (a/2) b (a%2) 1 hr (by simp)).mp (by simpa only [ha] using h2.2)
  have h4 : NoCarry a (2*b) := by
    have h4' := (noCarry_binary (a/2) b (a%2) 0 hr (by simp)).mpr ⟨by simpa using hr, h3.2⟩
    simpa only [ha, add_zero] using h4'
  have h5 := (noCarry_binary a (2*b) 0 1 (by simp) (by simp)).mpr ⟨by simp, h4⟩
  have h6 := (noCarry_binary (2*a) (2*(2*b)+1) 0 1 (by simp) (by simp)).mpr ⟨by simp, by simpa using h5⟩
  convert h6 using 1 <;> ring

#print axioms CompactHighOriginTransfer.transfer_parts
end CompactHighOriginTransfer
