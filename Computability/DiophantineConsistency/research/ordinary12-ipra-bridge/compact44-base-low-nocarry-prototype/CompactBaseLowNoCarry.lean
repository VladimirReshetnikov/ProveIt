import CompactCellDigitSupported
import CompactPackedCell
import DiophantineConsistency.CompactConcreteIncrement

/-! Base low-mask no-carry for a compact cell whose row is not forbidden. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactBaseLowNoCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticMaskConstants
open CompactCellDigit CompactCellDigitDef CompactPackedCell CompactCellDigitSupported

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One does not carry against an even model number. -/
theorem one_noCarry_even (y : V) (hy : y % 2 = 0) : NoCarry 1 y := by
  have he : 2 * (y / 2) + 0 = y := by simpa [hy] using div_add_mod y 2
  have hz : NoCarry (0 : V) (y / 2) := by rw [noCarry_iff]; intro i; simp
  have h := (noCarry_binary (0 : V) (y / 2) 1 0 (by simp) (by simp)).mpr ⟨by simp, hz⟩
  simpa only [mul_zero, zero_add, he] using h

/-- The concrete mask digit at each supported position has even parity. -/
theorem supported_mask_even (n : ℕ) (hn : n < 8807)
    (hs : n ∈ CompactConcreteMask.support) :
    dig 67 (CompactConcreteIncrement.mask : V) (n : V) % 2 = 0 := by
  have hd := dig_ofDigits (V:=V) 67
    (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)
    (CompactListMask.digits_lt _ _ _ _ (by norm_num)) n
  rw [CompactListMask.digits_getD _ _ _ _ hn] at hd
  change dig 67 (CompactConcreteIncrement.mask : V) (n : V) = _ at hd
  by_cases hsp : n = 1063
  · subst n
    simp only [CompactListMask.digit, if_true] at hd
    rw [hd]
    change (((2^67-4 : ℕ) : V) % ((2:ℕ):V)) = 0
    rw [← cast_mod]
    norm_num
  · simp only [CompactListMask.digit, hsp, if_false, hs, if_true] at hd
    rw [hd]
    change (((2^67-2 : ℕ) : V) % ((2:ℕ):V)) = 0
    rw [← cast_mod]
    norm_num

/-- All individual subdigits of the cell avoid the corresponding mask digit. -/
theorem local_noCarry (a k : V) (ha : a ≠ 1) (hk : k < 8807) :
    NoCarry (cellDigit a 0 k) (dig 67 (CompactConcreteIncrement.mask : V) k) := by
  have hb := cellDigit_le_one a 0 k (by simp)
  rcases le_one_iff_eq_zero_or_one.mp hb with hz | ho
  · rw [hz, noCarry_iff]; intro i; simp
  · obtain ⟨n, he, hs⟩ := cellDigit_supported a 0 k ha hk (by rw [ho]; simp)
    have hn : n < 8807 := by rw [he] at hk; exact_mod_cast hk
    rw [ho, he]
    exact one_noCarry_even _ (supported_mask_even n hn hs)

/-- The actual represented base cell is disjoint from the concrete mask. -/
theorem base_noCarry (a : V) (ha : a ≠ 1) :
    NoCarry (packedCell a 0) (CompactConcreteIncrement.mask : V) := by
  letI : 𝚺₁-Function₁ (cellDigit a (0 : V)) := cellDigit_definable a 0
  let g : V → V := fun j => dig 67 (CompactConcreteIncrement.mask : V) j
  letI : 𝚺₁-Function₁ g := by unfold g; definability
  have hmask : bsum 67 g 8807 = (CompactConcreteIncrement.mask : V) := by
    apply bsum_unique (f := g) (fun j _ => dig_lt 67 (CompactConcreteIncrement.mask : V) j)
    exact ⟨CompactConcreteMask.model_lt, fun j _ => rfl⟩
  have hc := bsum_noCarry (w := (67 : V)) (f := cellDigit a 0) (g := g) (n := 8807)
    (fun j _ => digit_bound a 0 (by simp) j) (fun j _ => dig_lt 67 _ j)
    (fun j hj => local_noCarry a j ha hj)
  unfold packedCell
  rwa [hmask] at hc

#print axioms CompactBaseLowNoCarry.one_noCarry_even
#print axioms CompactBaseLowNoCarry.supported_mask_even
#print axioms CompactBaseLowNoCarry.local_noCarry
#print axioms CompactBaseLowNoCarry.base_noCarry
end CompactBaseLowNoCarry
