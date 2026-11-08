import DiophantineConsistency.BFS943.DirectBFSPackedCell
import DiophantineConsistency.Compact44.CompactCellSupport
import DiophantineConsistency.Compact44.CompactConcreteIncrement

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSCellDigitSupported
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactCellCopyCode DirectBFSCellDigit CompactCellSupport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A forbidden selector row is the only way a nonzero selector could
    lie outside the concrete low-mask support. -/
theorem cellDigit_supported (a d k : V) (ha : a ≠ 1) (hk : k < 8807)
    (h : cellDigit a d k ≠ 0) :
    ∃ n : ℕ, k = (n : V) ∧ n ∈ CompactConcreteMask.support := by
  by_cases hs : k < 943
  · have he : a = k := by
      by_contra hn
      exact h (by simp [cellDigit, hs, hn])
    obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 8807) hk
    have hn : n < 943 := by exact_mod_cast hs
    have hne : n ≠ 1 := by
      intro hn1
      apply ha
      rw [he, hn1]
      simp
    refine ⟨n, rfl, ?_⟩
    simp [CompactConcreteMask.support, hn, hne]
  · by_cases hd : k = 1063
    · refine ⟨1063, ?_, ?_⟩
      · simpa using hd
      · exact CompactConcreteMask.special_mem
    · have hc : copyCode k ≠ 0 := by
        intro hc
        exact h (by simp [cellDigit, hs, hd, hc])
      exact copyCode_supported k hk hc

#print axioms DirectBFSCellDigitSupported.cellDigit_supported
end DirectBFSCellDigitSupported

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSBaseLowNoCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticMaskConstants
open DirectBFSCellDigit DirectBFSCellDigitUniform DirectBFSPackedCell DirectBFSCellDigitSupported

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
  letI : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := cellDigit_uniform
  haveI : 𝚺₁-Function₁ (cellDigit a (0 : V)) := by definability
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

#print axioms DirectBFSBaseLowNoCarry.one_noCarry_even
#print axioms DirectBFSBaseLowNoCarry.supported_mask_even
#print axioms DirectBFSBaseLowNoCarry.local_noCarry
#print axioms DirectBFSBaseLowNoCarry.base_noCarry
end DirectBFSBaseLowNoCarry
