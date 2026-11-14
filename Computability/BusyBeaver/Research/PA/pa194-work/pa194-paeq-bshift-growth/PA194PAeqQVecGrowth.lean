import PA194PAeqBShiftGrowth

/-! Explicit numeric growth of arithmetic quantifier vectors in every IΣ₁
model. The bound handles binary arithmetic function symbols. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqQVecGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessRepeatVec PA194PAeqBShiftGrowth

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem qVec_entries (w : V) : ∀ j, (qVec PA194PAeq.language w).[j] ≤ tau (w + 8) (20 * w + 20) := by
  intro j
  have h1 : (1 : V) ≤ tau (w + 8) (20 * w + 20) :=
    le_trans (by norm_num) (four_le_tau _ _)
  simp only [qVec]
  rcases zero_or_succ j with rfl | ⟨i, rfl⟩
  · simpa [qqBvar, pair] using h1
  · rw [nth_adjoin_succ]
    by_cases hv : IsUTermVec PA194PAeq.language (len w) w
    · by_cases hi : i < len w
      · rw [nth_termBShiftVec hv hi]
        apply le_trans (termBShift_le _)
        exact tau_mono (add_le_add (nth_le w i) le_rfl)
          (add_le_add (mul_le_mul' le_rfl (nth_le w i)) le_rfl)
      · rw [nth_lt_len (by rw [len_termBShiftVec hv]; exact not_lt.mp hi)]; simp
    · simp [termBShiftVec, hv]

theorem len_qVec_le (w : V) : len (qVec PA194PAeq.language w) ≤ w + 1 := by
  simp only [qVec, len_adjoin]
  refine add_le_add ?_ le_rfl
  by_cases hv : IsUTermVec PA194PAeq.language (len w) w
  · rw [len_termBShiftVec hv]; exact len_le w
  · simp [termBShiftVec, hv]

theorem qVec_le (w : V) : qVec PA194PAeq.language w ≤ tau (w + 8) (22 * w + 22) := by
  have he := qVec_entries w
  have h := len_repeatVec_of_nth_le (v := qVec PA194PAeq.language w)
    (m := tau (w + 8) (20 * w + 20)) (fun i _ => he i)
  refine le_trans h (le_trans (repeatVec_mono _ _ _ (len_qVec_le w))
    (le_trans (repeatVec_le_tau le_rfl (w + 1)) (tau_mono le_rfl ?_)))
  exact le_of_eq (by ring)

#print axioms qVec_le
end PA194PAeqQVecGrowth
