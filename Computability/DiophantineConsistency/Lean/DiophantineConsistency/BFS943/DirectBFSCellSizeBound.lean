import DiophantineConsistency.BFS943.DirectBFSCellLowMask

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSCellSizeBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticPackingBlocks
open DirectBFSCellDigit DirectBFSCellDigitUniform DirectBFSPackedCell DirectBFSCellDigitSupported
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem support_lt (n : ℕ) (hn : n ∈ CompactConcreteMask.support) : n < 3297 := by
  simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

theorem digit_zero_after (a d j : V) (ha : a ≠ 1) (hj : j < 8807)
    (hlo : 3297 ≤ j) : cellDigit a d j = 0 := by
  by_contra h
  obtain ⟨n, he, hs⟩ := cellDigit_supported a d j ha hj h
  have hn : (n : V) < 3297 := by exact_mod_cast support_lt n hs
  rw [← he] at hn
  exact (not_lt_of_ge hlo) hn

/-- The allocated 8807-slot cell has no nonzero digits at or beyond 3297. -/
theorem packedCell_lt_support (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    packedCell a d < Exp.exp (67*3297 : V) := by
  let f : V → V := cellDigit a d
  letI : 𝚺₁-Function₃ (cellDigit : V → V → V → V) := cellDigit_uniform
  haveI : 𝚺₁-Function₁ f := by unfold f; definability
  let y : V := bsum 67 f 3297
  have hy : y < Exp.exp (67*3297 : V) := bsum_lt (fun j _ => digit_bound a d hd j)
  have he : packedCell a d = y := by
    unfold packedCell
    apply bsum_unique (fun j _ => digit_bound a d hd j)
    constructor
    · exact lt_of_lt_of_le hy (exp_monotone_le.mpr (by norm_num : (67:V)*3297 ≤ 67*8807))
    · intro j hj
      by_cases hlow : j < 3297
      · exact dig_bsum (fun k _ => digit_bound a d hd k) hlow
      · have hge : 3297 ≤ j := not_lt.mp hlow
        have hjpow : Exp.exp (67*3297 : V) ≤ Exp.exp (67*j) :=
          exp_monotone_le.mpr (mul_le_mul_of_nonneg_left hge (by norm_num))
        have hz : dig 67 y j = 0 := by
          unfold dig
          rw [div_eq_zero_of_lt _ (lt_of_lt_of_le hy hjpow)]
          simp
        rw [hz]
        exact (digit_zero_after a d j ha hj hge).symm
  rw [he]
  exact hy

#print axioms DirectBFSCellSizeBound.support_lt
#print axioms DirectBFSCellSizeBound.digit_zero_after
#print axioms DirectBFSCellSizeBound.packedCell_lt_support
end DirectBFSCellSizeBound
