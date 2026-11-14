import PA196PAQVecGraph

/-! Arithmetic quantifier-vector length and entry bounds, valid also in
nonstandard IΣ₁ models. These do not assert a bound on the vector's code. -/
set_option autoImplicit false
namespace PA196PAQVecLength
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem len_qVec_le_len (w : V) : len (qVec ℒₒᵣ w) ≤ len w + 1 := by
  simp only [qVec, len_adjoin]
  refine add_le_add ?_ le_rfl
  by_cases hv : IsUTermVec ℒₒᵣ (len w) w
  · rw [len_termBShiftVec hv]
  · simp [termBShiftVec, hv]

theorem len_qVec_le (w : V) : len (qVec ℒₒᵣ w) ≤ w + 1 :=
  le_trans (len_qVec_le_len w) (add_le_add (len_le w) le_rfl)

theorem len_qVec_of_valid {w : V} (hw : IsUTermVec ℒₒᵣ (len w) w) :
    len (qVec ℒₒᵣ w) = len w + 1 := by
  simp [qVec, len_termBShiftVec hw]

theorem nth_qVec_succ {w i : V} (hw : IsUTermVec ℒₒᵣ (len w) w) (hi : i < len w) :
    (qVec ℒₒᵣ w).[i+1] = termBShift ℒₒᵣ w.[i] := by
  simp only [qVec, nth_adjoin_succ]
  exact nth_termBShiftVec hw hi

#print axioms len_qVec_le_len
#print axioms len_qVec_of_valid
#print axioms nth_qVec_succ
end PA196PAQVecLength
